#![feature(rustc_private)]

extern crate rustc_driver;

use std::{fs, path::Path};

use aquascope::interpreter::{InterpretCallbacks, InterpretOptions, OneCrate};

// A binary run as one crate with its package's library: the library's
// functions are stepped through and shown, with the binary's `main` below.
#[test_log::test]
fn a_binary_runs_as_one_crate_with_its_library() {
  let dir = std::env::temp_dir()
    .join(format!("aquascope-one-crate-{}", std::process::id()));
  let src = dir.join("src");
  fs::create_dir_all(&src).unwrap();
  fs::write(
    src.join("lib.rs"),
    "pub fn double(n: i32) -> i32 {\n  let d = n * 2;\n  d\n}\n",
  )
  .unwrap();
  fs::write(
    src.join("main.rs"),
    "use mini::double;\n\nfn main() {\n  let x = double(21);\n}\n",
  )
  .unwrap();

  let sysroot = aquascope_workspace_utils::miri_sysroot().unwrap();
  let lib = src.join("lib.rs").to_string_lossy().into_owned();
  let args = [
    "rustc",
    "--crate-name",
    "mini",
    "--edition=2024",
    &lib,
    "--crate-type",
    "lib",
    "--sysroot",
    &sysroot.to_string_lossy(),
    "-Zidentify-regions",
    "-Zmir-opt-level=0",
    "-Zmaximal-hir-to-mir-coverage",
    "-Awarnings",
  ]
  .map(String::from);
  let one_crate = OneCrate::new(&args, &src.join("main.rs")).unwrap();
  let args = one_crate.compiler_args(&args);
  let mut callbacks = InterpretCallbacks::new(false, InterpretOptions {
    one_crate: Some(one_crate),
    ..Default::default()
  });
  let _ = rustc_driver::catch_fatal_errors(|| {
    rustc_driver::run_compiler(&args, &mut callbacks)
  });
  fs::remove_dir_all(&dir).unwrap();

  let trace = callbacks.result.expect("the crate compiled").unwrap();
  let in_double = trace
    .steps
    .iter()
    .find(|step| step.stack.frames.last().unwrap().name == "double")
    .expect("a step in the library's function");
  let files = in_double
    .stack
    .frames
    .iter()
    .map(|frame| {
      let file = Path::new(&frame.file_path).file_name().unwrap();
      (frame.name.as_str(), file.to_string_lossy().into_owned())
    })
    .collect::<Vec<_>>();
  assert_eq!(files, [
    ("__aquascope_main::main", "main.rs".to_owned()),
    ("double", "lib.rs".to_owned())
  ]);
}
