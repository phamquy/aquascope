#![feature(rustc_private)]

use aquascope::{
  analysis::{AquascopeAnalysis, AquascopeError},
  test_utils,
};
use rustc_utils::test_utils::DUMMY_FILE_NAME;

// Each result names the file holding its body, and so does a build error, so
// that a caller analysing a crate of several files can place them.
#[test_log::test]
fn results_and_build_errors_name_their_file() {
  let code = r#"
fn builds() -> i32 {
  let x = 1;
  x
}

fn does_not_build() -> i32 {
  let x: i32 = "not a number";
  x
}
"#;

  let mut counts = (0, 0);
  test_utils::compile_normal(code, |tcx| {
    test_utils::for_each_body(tcx, |body_id, _| {
      match AquascopeAnalysis::run(tcx, body_id, false) {
        Ok(output) => {
          assert_eq!(output.file_path, DUMMY_FILE_NAME);
          counts.0 += 1;
        }
        Err(AquascopeError::BuildError { file_path, .. }) => {
          assert_eq!(file_path.as_deref(), Some(DUMMY_FILE_NAME));
          counts.1 += 1;
        }
        Err(e) => panic!("unexpected error: {e:?}"),
      }
    });
  });
  assert_eq!(counts, (1, 1), "one body built and one did not");
}

// Each frame of a trace names the file holding its function, so that a
// caller running a crate of several files can place each step.
#[test_log::test]
fn trace_frames_name_their_file() {
  let code = r#"
fn add(a: i32, b: i32) -> i32 {
  a + b
}

fn main() {
  let x = add(1, 2);
}
"#;
  let trace = test_utils::interpret_with(code, &Default::default()).unwrap();
  let frames = trace
    .steps
    .iter()
    .flat_map(|step| &step.stack.frames)
    .collect::<Vec<_>>();
  assert!(frames.iter().any(|frame| frame.name == "add"));
  for frame in frames {
    assert_eq!(frame.file_path, DUMMY_FILE_NAME, "frame {}", frame.name);
  }
}
