//! Rust runtime visualizer using Miri

use std::{
  io,
  path::{Path, PathBuf},
  sync::Arc,
};

use anyhow::{Context, Result};
use either::Either;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Body, ty::TyCtxt, util::Providers};
use rustc_utils::{SpanExt, source_map::range::CharRange};

mod mapper;
mod miri_utils;
mod mvalue;
mod step;

pub use mvalue::MValue;
use rustc_session::Session;
use rustc_span::source_map::{FileLoader, RealFileLoader};
pub use step::MTrace;

use crate::interpreter::mapper::Mapper;

/// How the interpreter runs the program.
#[derive(Debug, Default, Clone)]
pub struct InterpretOptions {
  /// Lift Miri's isolation, as `-Zmiri-disable-isolation` does, so that the
  /// program can use the file system, the clock and the environment.
  pub disable_isolation: bool,
  /// The program's command-line arguments. The program sees the crate's name
  /// before them, as a program run by Cargo sees its own.
  pub program_args: Vec<String>,
  /// Run a binary compiled together with its package's library.
  pub one_crate: Option<OneCrate>,
}

/// The module that holds a binary's root file in a `OneCrate` build.
pub const BIN_MODULE: &str = "__aquascope_main";

/// A binary compiled as a module of its package's library, so that the
/// library's functions are in the crate being interpreted, the only crate
/// whose functions the interpreter steps through and shows.
///
/// The library's root file is read with two lines added at its end, which
/// keeps every position in every file: `extern crate self as <library>;`, so
/// that the binary's `use <library>::...` names the crate itself, and a
/// `#[path]` module holding the binary's root file. The library is compiled
/// as an executable, which Miri requires, with `no_main`, and the run starts
/// at the `main` of that module.
#[derive(Debug, Clone)]
pub struct OneCrate {
  /// The library's root file, canonical, to recognise it when the compiler
  /// reads it.
  canonical_root: PathBuf,
  appendix: String,
}

impl OneCrate {
  /// `compiler_args` are the library's; `bin_file` is the binary's root file.
  pub fn new(compiler_args: &[String], bin_file: &Path) -> Result<Self> {
    let root = compiler_args
      .iter()
      .find(|arg| Path::new(arg).extension().is_some_and(|ext| ext == "rs"))
      .map(PathBuf::from)
      .context("no crate root in the compiler's arguments")?;
    let crate_name = compiler_args
      .iter()
      .position(|arg| arg == "--crate-name")
      .and_then(|i| compiler_args.get(i + 1))
      .context("no --crate-name in the compiler's arguments")?;
    let canonical_root = root
      .canonicalize()
      .with_context(|| format!("crate root {} not found", root.display()))?;
    let bin_file = bin_file
      .canonicalize()
      .with_context(|| format!("binary {} not found", bin_file.display()))?;
    let module_path =
      relative_path(canonical_root.parent().unwrap(), &bin_file);
    let appendix = format!(
      "\nextern crate self as {crate_name};\n#[path = {:?}]\nmod {BIN_MODULE};\n",
      module_path.to_string_lossy()
    );
    Ok(OneCrate {
      canonical_root,
      appendix,
    })
  }

  /// The library's compiler arguments, changed to compile an executable whose
  /// `main` is not at its root.
  pub fn compiler_args(&self, args: &[String]) -> Vec<String> {
    let mut out = Vec::with_capacity(args.len() + 1);
    let mut args = args.iter();
    while let Some(arg) = args.next() {
      if arg == "--crate-type" {
        args.next();
        out.extend(["--crate-type".to_owned(), "bin".to_owned()]);
      } else if arg.starts_with("--crate-type=") {
        out.push("--crate-type=bin".to_owned());
      } else {
        out.push(arg.clone());
      }
    }
    out.push("-Zcrate-attr=no_main".to_owned());
    out
  }

  fn file_loader(&self) -> OneCrateLoader {
    OneCrateLoader {
      root: self.canonical_root.clone(),
      appendix: self.appendix.clone(),
    }
  }
}

/// `target` relative to the folder `base`, both absolute.
fn relative_path(base: &Path, target: &Path) -> PathBuf {
  let base = base.components().collect::<Vec<_>>();
  let target = target.components().collect::<Vec<_>>();
  let common = base.iter().zip(&target).take_while(|(a, b)| a == b).count();
  let mut path = PathBuf::new();
  for _ in common .. base.len() {
    path.push("..");
  }
  for component in &target[common ..] {
    path.push(component);
  }
  path
}

/// Reads files from disk, adding a `OneCrate`'s lines to the library's root.
struct OneCrateLoader {
  root: PathBuf,
  appendix: String,
}

impl FileLoader for OneCrateLoader {
  fn file_exists(&self, path: &Path) -> bool {
    RealFileLoader.file_exists(path)
  }

  fn read_file(&self, path: &Path) -> io::Result<String> {
    let mut text = RealFileLoader.read_file(path)?;
    if path.canonicalize().is_ok_and(|path| path == self.root) {
      text.push_str(&self.appendix);
    }
    Ok(text)
  }

  fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
    RealFileLoader.read_binary_file(path)
  }

  fn current_directory(&self) -> io::Result<PathBuf> {
    RealFileLoader.current_directory()
  }
}

pub(crate) fn interpret(
  tcx: TyCtxt,
  options: &InterpretOptions,
) -> Result<MTrace<CharRange>> {
  let mut evaluator = step::VisEvaluator::new(tcx, options)?;
  let mir_steps = evaluator.eval()?;

  if log::log_enabled!(log::Level::Trace) {
    for step in &mir_steps.steps {
      let (inst, mir_body_loc) = step.stack.frames.last().unwrap().location;
      log::trace!("{}", match mir_body_loc {
        Either::Left(loc) => {
          let body = evaluator.ecx.load_mir(inst.def, None).unwrap();
          format!("{:?}", body.stmt_at(loc))
        }
        Either::Right(span) =>
          tcx.sess.source_map().span_to_snippet(span).unwrap(),
      })
    }
  }

  let mapper = Mapper::new(&evaluator.ecx);
  let hir_steps =
    mapper::group_steps(mir_steps, |loc| mapper.abstract_loc(loc));

  if log::log_enabled!(log::Level::Trace) {
    for step in &hir_steps.steps {
      let (_, hir_body_loc) = step.stack.frames.last().unwrap().location;
      log::trace!("{:?}", match hir_body_loc {
        Either::Left(node_id) => tcx.hir_id_to_string(node_id),
        Either::Right(span) =>
          tcx.sess.source_map().span_to_snippet(span).unwrap(),
      });
    }
  }

  let src_steps = mapper::group_steps(hir_steps, |(owner_id, hir_body_loc)| {
    let outer_span = tcx.hir_span_with_body(owner_id);
    let span = match hir_body_loc {
      Either::Left(node_id) => tcx.hir_span(node_id).as_local(outer_span)?,
      Either::Right(span) => span.as_local(outer_span)?,
    };
    let range = CharRange::from_span(span, tcx.sess.source_map()).unwrap();
    Some(range)
  });

  Ok(src_steps)
}

pub struct InterpretCallbacks {
  should_fail: bool,
  options: InterpretOptions,
  pub result: Option<Result<MTrace<CharRange>>>,
}

impl InterpretCallbacks {
  pub fn new(should_fail: bool, options: InterpretOptions) -> Self {
    InterpretCallbacks {
      should_fail,
      options,
      result: None,
    }
  }
}
// We disable `mir_borrowck` to allow programs with Rust-caught UB to execute
// rather than being rejected out of hand.
fn fake_mir_borrowck(
  tcx: TyCtxt<'_>,
  _id: LocalDefId,
) -> rustc_middle::queries::mir_borrowck::ProvidedValue<'_> {
  Ok(tcx.arena.alloc(FxIndexMap::default()))
}

// Some optimizations like drop elaboration depend on MoveData, and will raise an error
// if the MoveData is empty. Thankfully we can reset and ignore that error via
// `Handler::reset_err_count` which we do by overriding optimized_mir.
fn fake_optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &'_ Body<'_> {
  let mut providers = Providers::default();
  rustc_mir_transform::provide(&mut providers);
  let body = (providers.queries.optimized_mir)(tcx, did);
  tcx.sess.dcx().reset_err_count();
  body
}

// See `fake_mir_borrowck`
pub fn override_queries(
  _session: &Session,
  providers: &mut rustc_middle::util::Providers,
) {
  providers.queries.mir_borrowck = fake_mir_borrowck;
  providers.queries.optimized_mir = fake_optimized_mir;
}

impl rustc_driver::Callbacks for InterpretCallbacks {
  // See `fake_mir_borrowck`
  fn config(&mut self, config: &mut rustc_interface::interface::Config) {
    if self.should_fail {
      config.override_queries = Some(override_queries);
    }
    if let Some(one_crate) = &self.options.one_crate {
      config.file_loader = Some(Box::new(one_crate.file_loader()));
    }
  }

  fn after_analysis(
    &mut self,
    _compiler: &rustc_interface::interface::Compiler,
    tcx: TyCtxt<'_>,
  ) -> rustc_driver::Compilation {
    self.result = Some(interpret(tcx, &self.options));
    rustc_driver::Compilation::Stop
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn relative_paths() {
    let path = |s: &str| PathBuf::from(s);
    assert_eq!(
      relative_path(&path("/p/src"), &path("/p/src/main.rs")),
      path("main.rs")
    );
    assert_eq!(
      relative_path(&path("/p/src"), &path("/p/src/bin/tool.rs")),
      path("bin/tool.rs")
    );
    assert_eq!(
      relative_path(&path("/p/lib"), &path("/p/src/main.rs")),
      path("../src/main.rs")
    );
  }

  #[test]
  fn one_crate_compiles_an_executable_without_main() {
    let one_crate = OneCrate {
      canonical_root: PathBuf::from("/p/src/lib.rs"),
      appendix: String::new(),
    };
    let args = ["--crate-name", "mini", "src/lib.rs", "--crate-type", "lib"]
      .map(String::from);
    assert_eq!(one_crate.compiler_args(&args), [
      "--crate-name",
      "mini",
      "src/lib.rs",
      "--crate-type",
      "bin",
      "-Zcrate-attr=no_main"
    ]);
  }
}
