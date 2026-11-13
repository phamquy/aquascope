#![feature(rustc_private)]

use aquascope::{analysis::AquascopeAnalysis, test_utils};

// The stepper cannot yet segment a branch that leaves the body early when
// another branch follows it (#157). The analysis of such a body should still
// succeed with its permission boundaries, rather than fail as a whole.
#[test_log::test]
fn early_return_keeps_boundaries() {
  let code = r#"
fn parse(mut args: impl Iterator<Item = String>) -> Result<(String, String), String> {
  let query = match args.next() {
    Some(arg) => arg,
    None => return Err("Missing query".into()),
  };
  let path = match args.next() {
    Some(arg) => arg,
    None => return Err("Missing path".into()),
  };
  Ok((query, path))
}

fn both(v: Vec<i32>) -> Option<i32> {
  let mut it = v.into_iter();
  let x = it.next()?;
  let y = it.next()?;
  Some(x + y)
}
"#;

  test_utils::compile_normal(code, |tcx| {
    test_utils::for_each_body(tcx, |body_id, _| {
      let output = match AquascopeAnalysis::run(tcx, body_id, false) {
        Ok(output) => output,
        Err(e) => panic!("the analysis failed: {e:?}"),
      };
      assert!(!output.boundaries.is_empty(), "no boundaries");
    });
  });
}

// A branch whose arm leaves the body, by `return`, `?` or a call that never
// returns, takes its join point from the arms that continue, so the code
// after it is stepped. A `let … else` is such a branch on its pattern.
#[test_log::test]
fn early_exits_get_steps() {
  let code = r#"
fn parse(mut args: impl Iterator<Item = String>) -> Result<(String, String), String> {
  let query = match args.next() {
    Some(arg) => arg,
    None => return Err("Missing query".into()),
  };
  let path = match args.next() {
    Some(arg) => arg,
    None => return Err("Missing path".into()),
  };
  Ok((query, path))
}

fn both(v: Vec<i32>) -> Option<i32> {
  let mut it = v.into_iter();
  let x = it.next()?;
  let y = it.next()?;
  if x > y { Some(x) } else { Some(y) }
}

fn first_len(v: Vec<String>, flag: bool) -> usize {
  let s = String::from("a");
  if flag {
    return 0;
  }
  let t = s;
  if v.is_empty() { 1 } else { t.len() }
}

fn let_else(v: Vec<String>, d: String) -> usize {
  let Some(s) = v.first() else {
    return d.len();
  };
  if s.is_empty() { d.len() } else { s.len() }
}

fn nested_let_else(v: Vec<Result<i32, String>>, d: i32) -> i32 {
  let Some(Ok(x)) = v.into_iter().next() else {
    return d;
  };
  if x > d { x } else { d }
}
"#;

  test_utils::compile_normal(code, |tcx| {
    test_utils::for_each_body(tcx, |body_id, _| {
      let output = match AquascopeAnalysis::run(tcx, body_id, false) {
        Ok(output) => output,
        Err(e) => panic!("the analysis failed: {e:?}"),
      };
      assert!(!output.boundaries.is_empty(), "no boundaries");
      assert!(!output.steps.is_empty(), "no steps");
    });
  });
}

// Two shapes the stepper still cannot segment: an `if` chain where every arm
// returns, with a `match` on a tuple inside, and `break` out of a `loop`
// followed by more code. They keep their boundaries and get no steps, and
// the stepper fails with an error, not a panic.
#[test_log::test]
fn shapes_left_for_later_keep_boundaries_without_steps() {
  let code = r#"
struct Node {
  key: i32,
  left: Option<Box<Node>>,
  right: Option<Box<Node>>,
}

fn remove_rec(node: &mut Option<Box<Node>>, key: i32) -> bool {
  if let Some(n) = node {
    if key < n.key {
      return remove_rec(&mut n.left, key);
    } else if key > n.key {
      return remove_rec(&mut n.right, key);
    } else {
      *node = match (n.left.take(), n.right.take()) {
        (None, None) => None,
        (Some(left), None) => Some(left),
        (None, Some(right)) => Some(right),
        (Some(left), Some(right)) => {
          let mut min = right;
          let mut min_ref = &mut min;
          while let Some(ref mut l) = min_ref.left {
            min_ref = l;
          }
          min_ref.left = Some(left);
          Some(min)
        }
      };
      return true;
    }
  }
  false
}

fn bump_all(v: &mut Vec<i32>) -> i32 {
  let mut i = 0;
  loop {
    if i >= v.len() {
      break;
    }
    v[i] += 1;
    i += 1;
  }
  if i > 0 { 1 } else { 0 }
}
"#;

  test_utils::compile_normal(code, |tcx| {
    test_utils::for_each_body(tcx, |body_id, _| {
      let output = match AquascopeAnalysis::run(tcx, body_id, false) {
        Ok(output) => output,
        Err(e) => panic!("the analysis failed: {e:?}"),
      };
      assert!(!output.boundaries.is_empty(), "no boundaries");
      assert!(
        output.steps.is_empty(),
        "steps, which this test does not expect yet"
      );
    });
  });
}

// A plain `loop` with `if … { break; }` makes the stepper panic (#68). The
// panic is caught like the stepper's errors: that body keeps its boundaries
// and gets no steps, and the other bodies of the crate are analysed as usual.
#[test_log::test]
fn stepper_panic_keeps_boundaries() {
  let code = r#"
fn count(v: &Vec<i32>) -> usize {
  let mut i = 0;
  loop {
    if i >= v.len() {
      break;
    }
    i += 1;
  }
  i
}

fn after(s: String) -> usize {
  let t = s;
  t.len()
}
"#;

  test_utils::compile_normal(code, |tcx| {
    test_utils::for_each_body(tcx, |body_id, _| {
      let name = tcx
        .hir_opt_name(tcx.hir_body_owner(body_id))
        .map(|s| s.to_string());
      let output = match AquascopeAnalysis::run(tcx, body_id, false) {
        Ok(output) => output,
        Err(e) => panic!("the analysis of {name:?} failed: {e:?}"),
      };
      assert!(!output.boundaries.is_empty(), "{name:?}: no boundaries");
      match name.as_deref() {
        Some("count") => assert!(output.steps.is_empty(), "count: steps"),
        Some("after") => assert!(!output.steps.is_empty(), "after: no steps"),
        other => panic!("unexpected body {other:?}"),
      }
    });
  });
}
