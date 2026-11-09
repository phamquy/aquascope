use std::{
  borrow::Cow,
  env,
  path::PathBuf,
  process::{Command, exit},
  time::Instant,
};

use aquascope::{
  analysis::{
    self, AnalysisOutput, AquascopeError, AquascopeResult,
    permissions::ENABLE_FLOW_PERMISSIONS,
    stepper::{INCLUDE_MODE, PermIncludeMode},
  },
  errors::{
    initialize_error_tracking, silent::silent_session, track_body_diagnostics,
  },
  interpreter::OneCrate,
};
use clap::{Parser, Subcommand};
use fluid_let::fluid_set;
use rustc_interface::interface::Result as RustcResult;
use rustc_middle::ty::TyCtxt;
use rustc_plugin::{CrateFilter, RustcPlugin, RustcPluginArgs, Utf8Path};
use rustc_utils::{mir::borrowck_facts, source_map::find_bodies::find_bodies};
use serde::{self, Deserialize, Serialize};

const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Debug, Parser, Serialize, Deserialize)]
#[clap(version = VERSION)]
pub struct AquascopePluginArgs {
  #[clap(long)]
  should_fail: bool,

  /// Analyse only the crate containing this file, instead of every crate of
  /// the workspace.
  #[clap(long, value_name = "FILE")]
  crate_of: Option<PathBuf>,

  #[clap(subcommand)]
  command: AquascopeCommand,
}

#[derive(Debug, Subcommand, Serialize, Deserialize)]
enum AquascopeCommand {
  Permissions {
    #[clap(long)]
    steps_include_mode: Option<PermIncludeMode>,

    #[clap(long)]
    show_flows: bool,
  },

  Interpreter {
    /// Lift Miri's isolation, as `-Zmiri-disable-isolation` does, so that the
    /// program can use the file system, the clock and the environment.
    #[clap(long)]
    disable_isolation: bool,

    /// Run the binary whose root file this is, compiled as one crate with
    /// its package's library, so that the library's functions are shown too.
    /// `--crate-of` names the library.
    #[clap(long, value_name = "FILE")]
    bin_file: Option<PathBuf>,

    /// The program's command-line arguments, after `--`.
    #[clap(last = true)]
    program_args: Vec<String>,
  },

  Preload,
  RustcVersion,
}

impl AquascopePluginArgs {
  /// The crates to analyse. In a workspace, the analysis of a crate stops
  /// before writing the metadata that crates depending on it need, so in the
  /// default whole-workspace run those crates get no results; `--crate-of`
  /// builds them normally and analyses only the crate holding the file.
  fn crate_filter(&self) -> CrateFilter {
    match &self.crate_of {
      Some(file) => CrateFilter::CrateContainingFile(file.clone()),
      None => CrateFilter::OnlyWorkspace,
    }
  }
}

/// The cargo arguments and the encoded `CARGO_ENCODED_RUSTFLAGS` that build
/// every crate as `cargo miri` does, so that the interpreter can run the
/// functions of other crates: with Miri's standard library and with each
/// function's MIR kept in the crate's metadata. Naming the host as the target
/// keeps these flags from build scripts and proc macros, which run natively.
/// `existing` holds the flags already given, which are kept.
fn miri_build(
  sysroot: &str,
  host: &str,
  existing: Vec<String>,
) -> ([String; 2], String) {
  let mut flags = existing;
  flags.extend([
    "--sysroot".to_owned(),
    sysroot.to_owned(),
    "-Zalways-encode-mir".to_owned(),
  ]);
  (["--target".to_owned(), host.to_owned()], flags.join("\x1f"))
}

/// The compiler flags Cargo would take from the environment.
fn existing_rustflags() -> Vec<String> {
  match env::var("CARGO_ENCODED_RUSTFLAGS") {
    Ok(encoded) if !encoded.is_empty() => {
      encoded.split('\x1f').map(str::to_owned).collect()
    }
    _ => env::var("RUSTFLAGS")
      .map(|flags| flags.split_whitespace().map(str::to_owned).collect())
      .unwrap_or_default(),
  }
}

pub struct AquascopePlugin;
impl RustcPlugin for AquascopePlugin {
  type Args = AquascopePluginArgs;

  fn version(&self) -> Cow<'static, str> {
    env!("CARGO_PKG_VERSION").into()
  }

  fn driver_name(&self) -> Cow<'static, str> {
    "aquascope-driver".into()
  }

  fn args(
    &self,
    target_dir: &Utf8Path,
  ) -> RustcPluginArgs<AquascopePluginArgs> {
    let mut args = AquascopePluginArgs::parse_from(env::args().skip(1));
    // The compiler runs in the workspace root, not here.
    if let AquascopeCommand::Interpreter {
      bin_file: Some(file),
      ..
    } = &mut args.command
    {
      *file = file.canonicalize().unwrap_or_else(|e| {
        eprintln!("--bin-file {}: {e}", file.display());
        exit(2)
      });
    }

    log::debug!("Provided PluginArgs {args:?}");

    let cargo_path =
      env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());

    use AquascopeCommand::*;
    match &args.command {
      Preload => {
        let mut cmd = Command::new(cargo_path);
        // Note: this command must share certain parameters with rustc_plugin so Cargo will not recompute
        // dependencies when actually running the driver, e.g. RUSTFLAGS.
        cmd
          .args(["check", "--all", "--all-features", "--target-dir"])
          .arg(target_dir)
          .env("RUSTFLAGS", "-Awarnings");
        let exit_status = cmd.status().expect("could not run cargo");
        exit(exit_status.code().unwrap_or(-1));
      }
      RustcVersion => {
        let commit_hash =
          rustc_interface::util::rustc_version_str().unwrap_or("unknown");
        println!("{commit_hash}");
        exit(0);
      }
      _ => {}
    };

    RustcPluginArgs {
      filter: args.crate_filter(),
      args,
    }
  }

  fn modify_cargo(&self, cargo: &mut Command, args: &Self::Args) {
    // Without Miri's standard library, the interpreter has nothing to run
    // with, so only then is every crate built for it.
    if let (AquascopeCommand::Interpreter { .. }, Ok(sysroot)) =
      (&args.command, env::var("MIRI_SYSROOT"))
    {
      let (target, flags) = miri_build(
        &sysroot,
        rustc_session::config::host_tuple(),
        existing_rustflags(),
      );
      cargo.args(target).env("CARGO_ENCODED_RUSTFLAGS", flags);
    }
  }

  fn run(
    self,
    compiler_args: Vec<String>,
    plugin_args: AquascopePluginArgs,
  ) -> RustcResult<()> {
    use AquascopeCommand::*;
    match plugin_args.command {
      Permissions {
        steps_include_mode,
        show_flows,
        ..
      } => {
        let steps_include_mode =
          steps_include_mode.unwrap_or(PermIncludeMode::Changes);
        let mut callbacks = AquascopeCallbacks {
          output: Vec::default(),
          should_fail: plugin_args.should_fail,
          steps_include_mode,
          show_flows,
          rustc_start: Instant::now(),
        };
        log::info!("Starting rustc analysis...");
        let _ = run_with_callbacks(&compiler_args, &mut callbacks);
        postprocess(callbacks.output)
      }
      Interpreter {
        disable_isolation,
        bin_file,
        program_args,
      } => {
        let one_crate = match bin_file
          .map(|file| OneCrate::new(&compiler_args, &file))
          .transpose()
        {
          Ok(one_crate) => one_crate,
          Err(e) => {
            eprintln!("aquascope interpreter: {e:#}");
            return postprocess(Err::<(), _>(AquascopeError::BuildError {
              range: None,
              file_path: None,
            }));
          }
        };
        let compiler_args = match &one_crate {
          Some(one_crate) => one_crate.compiler_args(&compiler_args),
          None => compiler_args,
        };
        let mut callbacks = aquascope::interpreter::InterpretCallbacks::new(
          plugin_args.should_fail,
          aquascope::interpreter::InterpretOptions {
            disable_isolation,
            program_args,
            one_crate,
          },
        );
        let _ = run_with_callbacks(&compiler_args, &mut callbacks);
        postprocess(callbacks.result.unwrap().map_err(|e| {
          // The output has no place for the reason, such as the program's
          // exit code or an operation isolation refused, so it goes to stderr.
          eprintln!("aquascope interpreter: {e:#}");
          AquascopeError::BuildError {
            range: None,
            file_path: None,
          }
        }))
      }
      _ => unreachable!(),
    }
  }
}

fn postprocess<T: Serialize>(result: T) -> RustcResult<()> {
  println!("{}", serde_json::to_string(&result).unwrap());
  Ok(())
}

pub fn run_with_callbacks(
  args: &[String],
  callbacks: &mut (dyn rustc_driver::Callbacks + Send),
) -> AquascopeResult<()> {
  let mut args = args.to_vec();
  args.extend(
    "-Z identify-regions -Z mir-opt-level=0 -Z track-diagnostics=yes -Z maximal-hir-to-mir-coverage -A warnings"
      .split(' ')
      .map(|s| s.to_owned()),
  );

  log::debug!("Running command with callbacks: {args:?}");

  rustc_driver::catch_fatal_errors(move || {
    rustc_driver::run_compiler(&args, callbacks)
  })
  .map_err(|_| AquascopeError::BuildError {
    range: None,
    file_path: None,
  })
}

#[allow(dead_code)]
struct AquascopeCallbacks {
  output: Vec<AquascopeResult<AnalysisOutput>>,
  should_fail: bool,
  steps_include_mode: PermIncludeMode,
  show_flows: bool,
  rustc_start: Instant,
}

impl rustc_driver::Callbacks for AquascopeCallbacks {
  fn config(&mut self, config: &mut rustc_interface::Config) {
    config.psess_created = Some(silent_session());
    config.override_queries = Some(borrowck_facts::override_queries);
  }

  fn after_expansion(
    &mut self,
    _compiler: &rustc_interface::interface::Compiler,
    tcx: TyCtxt<'_>,
  ) -> rustc_driver::Compilation {
    // Setting up error tracking happens here. Within rustc callbacks
    // seem to be set up *after* `config` is called.
    initialize_error_tracking();

    fluid_set!(INCLUDE_MODE, self.steps_include_mode);
    fluid_set!(ENABLE_FLOW_PERMISSIONS, self.show_flows);

    let _start = Instant::now();

    find_bodies(tcx).into_iter().for_each(|(_, body_id)| {
      // Track diagnostics for the analysis of the current body
      let def_id = tcx.hir_body_owner_def_id(body_id);
      track_body_diagnostics(def_id);
      self.output.push(analysis::AquascopeAnalysis::run(
        tcx,
        body_id,
        self.should_fail,
      ));
    });

    log::debug!("Callback analysis took {:?}", self.rustc_start.elapsed());

    rustc_driver::Compilation::Stop
  }
}

#[cfg(test)]
mod tests {
  use std::path::Path;

  use super::*;

  #[test]
  fn crate_of_selects_the_crate_containing_the_file() {
    let args = AquascopePluginArgs::parse_from([
      "cargo-aquascope",
      "--crate-of",
      "src/lib.rs",
      "permissions",
    ]);
    assert!(matches!(
      args.crate_filter(),
      CrateFilter::CrateContainingFile(file) if file.as_path() == Path::new("src/lib.rs")
    ));

    let args =
      AquascopePluginArgs::parse_from(["cargo-aquascope", "permissions"]);
    assert!(matches!(args.crate_filter(), CrateFilter::OnlyWorkspace));
  }

  #[test]
  fn the_interpreter_builds_every_crate_as_cargo_miri_does() {
    let (target, flags) = miri_build("/sysroot", "aarch64-apple-darwin", vec![
      "-Awarnings".to_owned(),
    ]);
    assert_eq!(target, ["--target", "aarch64-apple-darwin"]);
    assert_eq!(flags.split('\x1f').collect::<Vec<_>>(), [
      "-Awarnings",
      "--sysroot",
      "/sysroot",
      "-Zalways-encode-mir"
    ]);
  }
}
