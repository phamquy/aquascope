use miri::{
  InterpCx, InterpResult, MPlaceTy, Machine, MemPlaceMeta, OpTy, Projectable,
  interp_ok,
};
use rustc_abi::{FieldIdx, FieldsShape, Size};
use rustc_middle::{
  mir::{Local, PlaceElem, interpret::Pointer},
  ty::{AdtKind, FieldDef, TyKind, layout::TyAndLayout},
};

pub trait OpTyExt<'tcx, M: Machine<'tcx>>: Sized {
  fn field_by_name(
    &self,
    name: &str,
    ecx: &InterpCx<'tcx, M>,
  ) -> InterpResult<'tcx, (&FieldDef, Self)>;
}

impl<'tcx, M> OpTyExt<'tcx, M> for OpTy<'tcx>
where
  M: Machine<'tcx>,
  Self: Projectable<'tcx, M::Provenance>,
{
  fn field_by_name(
    &self,
    name: &str,
    ecx: &InterpCx<'tcx, M>,
  ) -> InterpResult<'tcx, (&FieldDef, Self)> {
    let adt_def = self.layout.ty.ty_adt_def().unwrap();
    let (i, field) = adt_def
      .all_fields()
      .enumerate()
      .find(|(_, field)| field.name.as_str() == name)
      .unwrap_or_else(|| {
        panic!(
          "Could not find field with name `{name}` out of fields: {:?}",
          adt_def
            .all_fields()
            .map(|field| field.name)
            .collect::<Vec<_>>()
        )
      });
    let field_op = ecx.project_field(self, FieldIdx::from_usize(i))?;
    interp_ok((field, field_op))
  }
}

struct AddressLocator<'a, 'tcx> {
  ecx: &'a InterpCx<'tcx, miri::MiriMachine<'tcx>>,
  /// The start of the allocation that `target` is an offset into.
  start: Pointer<Option<miri::Provenance>>,
  target: u64,
  segments: Vec<PlaceElem<'tcx>>,
}

impl<'tcx> AddressLocator<'_, 'tcx> {
  fn locate(&mut self, layout: TyAndLayout<'tcx>, offset: u64) {
    if offset == self.target {
      return;
    }

    let ty = layout.ty;
    match ty.kind() {
      TyKind::Adt(adt_def, _) => {
        let def_id = adt_def.did();
        let name = self.ecx.tcx.item_name(def_id).to_ident_string();
        match adt_def.adt_kind() {
          AdtKind::Struct => match name.as_str() {
            "String" | "Vec" => {}
            _ => self.locate_in_fields(layout, offset),
          },
          // An enum's fields are those of the variant its value holds, which
          // its tag in memory says, in the variant's own layout. They are
          // numbered as the interpreter reads an enum's value: the variant's
          // fields alone.
          AdtKind::Enum => {
            let at = self
              .start
              .wrapping_offset(Size::from_bytes(offset), self.ecx);
            let place = self.ecx.ptr_to_mplace(at, layout);
            if let Some(variant) =
              self.ecx.read_discriminant(&place).discard_err()
            {
              self.locate_in_fields(
                layout.for_variant(self.ecx, variant),
                offset,
              );
            }
          }
          _ => {}
        }
      }

      TyKind::Array(_, _) => {
        // dbg!(("array", offset, target));
        let FieldsShape::Array { stride, .. } = layout.layout.fields() else {
          unreachable!()
        };
        let stride = stride.bytes();
        let array_offset = (self.target - offset) / stride * stride;
        let elem = layout.field(self.ecx, 0);
        let index = (array_offset / stride) as usize;
        // dbg!((index, array_offset));
        self
          .segments
          .push(PlaceElem::Index(Local::from_usize(index)));
        self.locate(elem, offset + array_offset);
      }

      TyKind::Tuple(_) => self.locate_in_fields(layout, offset),

      _ if ty.is_primitive() || ty.is_any_ptr() => {
        panic!("offset {offset} != target {}", self.target)
      }

      ty => unimplemented!("{ty:#?}"),
    }
  }

  /// Goes into the field of `layout`, a value at `offset` in the allocation,
  /// that holds the target. The fields are found at their offsets in the
  /// layout, since rustc reorders the fields of structs, tuples and variants
  /// and pads them; a target in no field, such as in padding, stays at the
  /// value as a whole.
  fn locate_in_fields(&mut self, layout: TyAndLayout<'tcx>, offset: u64) {
    for i in 0 .. layout.fields.count() {
      let start = offset + layout.fields.offset(i).bytes();
      let field = layout.field(self.ecx, i);
      if (start .. start + field.size.bytes()).contains(&self.target) {
        self
          .segments
          .push(PlaceElem::Field(FieldIdx::from_usize(i), field.ty));
        self.locate(field, start);
        return;
      }
    }
  }
}

pub fn locate_address_in_type<'tcx>(
  ecx: &InterpCx<'tcx, miri::MiriMachine<'tcx>>,
  alloc_layout: TyAndLayout<'tcx>,
  alloc_size: Size,
  mplace: MPlaceTy<'tcx>,
  target: Size,
) -> Vec<PlaceElem<'tcx>> {
  // dbg!((alloc_layout, alloc_size, mplace, target));
  let mut locator = AddressLocator {
    ecx,
    start: mplace
      .ptr()
      .wrapping_signed_offset(-(target.bytes() as i64), ecx),
    target: target.bytes(),
    segments: Vec::new(),
  };

  let mut offset = 0;
  if alloc_layout.size.bytes() < alloc_size.bytes() {
    let array_elem_size = alloc_layout.size.bytes();
    assert!(
      array_elem_size > 0,
      "Array has zero-sized elements: {alloc_layout:#?}"
    );

    offset = target.bytes() / array_elem_size * array_elem_size;
    let index = offset / array_elem_size;
    // dbg!((array_elem_size, offset, index));

    let segment = match mplace.meta() {
      // A slice's metadata is its number of elements, not its size in bytes,
      // which only a slice of bytes, such as a `str`, has the same.
      // An empty slice has no last element, so it is located at its first.
      MemPlaceMeta::Meta(meta) => match meta.to_u64().unwrap() {
        0 => PlaceElem::Index(Local::from_usize(index as usize)),
        len => PlaceElem::Subslice {
          from: index,
          to: index + len - 1,
          from_end: false,
        },
      },
      MemPlaceMeta::None => PlaceElem::Index(Local::from_usize(index as usize)),
    };

    locator.segments.push(segment);
  }

  locator.locate(alloc_layout, offset);
  locator.segments
}
