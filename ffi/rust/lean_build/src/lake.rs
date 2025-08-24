use std::error::Error;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

mod env;
mod package;

pub use env::get_lake_environment;
pub use package::{LakeBuildOutputTraversalEvent, LakeBuildOutputTraverser, find_c_files};

fn display_slice(slice: &[u8]) -> &str {
    str::from_utf8(slice).unwrap_or("[Non-UTF8]")
}

pub struct LakeLibraryDescription<'a, P: AsRef<Path>, Q: AsRef<Path> = PathBuf> {
    pub lake_package_path: P,
    pub target_name: &'a str,
    /// The directory containing the library's Lean source files, used for
    /// change detection. Defaults to `lake_package_path`
    pub source_directory: Option<Q>,
}

impl<'a, P: AsRef<Path>, Q: AsRef<Path>> LakeLibraryDescription<'a, P, Q> {
    fn get_source_directory(&self) -> &Path {
        match self.source_directory.as_ref() {
            Some(source_directory) => source_directory.as_ref(),
            None => self.lake_package_path.as_ref(),
        }
    }
}

fn run_lake_command_and_retrieve_stdout<'a>(
    args: &'a [&'a OsStr],
) -> Result<Vec<u8>, Box<dyn Error>> {
    let output = Command::new("lake").args(args).output()?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(format!(
            "Lake invocation with arguments {args:?} failed with status {}, stdout:{}, stderr: {}",
            output.status,
            display_slice(&output.stdout),
            display_slice(&output.stderr),
        )
        .into())
    }
}

/// Assumes there is only a single target path
fn get_lake_target_path_from_lake_query_output(
    lean_build_output: &[u8],
) -> Result<PathBuf, Box<dyn Error>> {
    let output_str = str::from_utf8(lean_build_output)
        .map_err(|err| format!("Lake query output is not valid UTF8: {err}"))?;
    Ok(Path::new(output_str).to_path_buf())
}

fn rerun_build_if_lake_package_changes<P: AsRef<Path>, Q: AsRef<Path>>(
    lake_library_description: &LakeLibraryDescription<P, Q>,
) {
    println!(
        "cargo:rerun-if-changed={}",
        lake_library_description.get_source_directory().display()
    );
}

pub fn build_and_link_static_lean_library<P: AsRef<Path>, Q: AsRef<Path>>(
    lake_library_description: &LakeLibraryDescription<P, Q>,
) -> Result<(), Box<dyn Error>> {
    let lake_package_path = lake_library_description.lake_package_path.as_ref();
    let build_target = format!("@/{}:static", lake_library_description.target_name);
    let args = [
        OsStr::new("--dir"),
        lake_package_path.as_os_str(),
        OsStr::new("query"),
        OsStr::new("--text"),
        OsStr::new(&build_target),
    ];
    let stdout = run_lake_command_and_retrieve_stdout(&args)?;
    let library_path = get_lake_target_path_from_lake_query_output(&stdout)?;
    if let Some(library_directory) = library_path.parent() {
        println!("cargo:rustc-link-search={}", library_directory.display());
    }
    println!(
        "cargo:rustc-link-lib=static={}",
        lake_library_description.target_name
    );

    rerun_build_if_lake_package_changes(lake_library_description);
    Ok(())
}
