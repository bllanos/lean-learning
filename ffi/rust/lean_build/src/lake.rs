use std::error::Error;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

use glob::MatchOptions;

fn display_slice(slice: &[u8]) -> &str {
    str::from_utf8(slice).unwrap_or("[Non-UTF8]")
}

pub struct LakeEnv {
    elan_toolchain: String,
    lean_githash: String,
    lean_sysroot: PathBuf,
}

impl LakeEnv {
    const ELAN_TOOLCHAIN: &str = "ELAN_TOOLCHAIN";
    const LEAN_GITHASH: &str = "LEAN_GITHASH";
    const LEAN_SYSROOT: &str = "LEAN_SYSROOT";

    pub fn from_posix_env(env: &[u8]) -> Result<Self, Box<dyn Error>> {
        let tuple = env.split(|c| c.is_ascii_control()).try_fold(
            (String::new(), String::new(), PathBuf::new()),
            |accumulator, slice| -> Result<(String, String, PathBuf), Box<dyn Error>> {
                let mut parts = slice.splitn(2, |c| *c == b'=');
                let var = parts.next().ok_or_else(|| {
                    format!(
                        "no variable name in environment line \"{}\"",
                        display_slice(slice)
                    )
                })?;
                match parts.next() {
                    None => Ok(accumulator),
                    Some(value) => {
                        let var_str = str::from_utf8(var)?;
                        match var_str {
                            Self::ELAN_TOOLCHAIN => {
                                let value_str = str::from_utf8(value)?;
                                if accumulator.0.is_empty() {
                                    Ok((String::from(value_str), accumulator.1, accumulator.2))
                                } else {
                                    Err(format!(
                                        "duplicate {} variable in environment string",
                                        Self::ELAN_TOOLCHAIN
                                    )
                                    .into())
                                }
                            }
                            Self::LEAN_GITHASH => {
                                let value_str = str::from_utf8(value)?;
                                if accumulator.1.is_empty() {
                                    Ok((accumulator.0, String::from(value_str), accumulator.2))
                                } else {
                                    Err(format!(
                                        "duplicate {} variable in environment string",
                                        Self::LEAN_GITHASH
                                    )
                                    .into())
                                }
                            }
                            Self::LEAN_SYSROOT => {
                                let value_str = str::from_utf8(value)?;
                                if accumulator.2.as_os_str().is_empty() {
                                    Ok((accumulator.0, accumulator.1, PathBuf::from(value_str)))
                                } else {
                                    Err(format!(
                                        "duplicate {} variable in environment string",
                                        Self::LEAN_SYSROOT
                                    )
                                    .into())
                                }
                            }
                            _ => Ok(accumulator),
                        }
                    }
                }
            },
        )?;
        if tuple.0.is_empty() {
            Err(format!(
                "missing {} variable in environment string",
                Self::ELAN_TOOLCHAIN
            )
            .into())
        } else if tuple.1.is_empty() {
            Err(format!(
                "missing {} variable in environment string",
                Self::LEAN_GITHASH
            )
            .into())
        } else if tuple.2.as_os_str().is_empty() {
            Err(format!(
                "missing {} variable in environment string",
                Self::LEAN_SYSROOT
            )
            .into())
        } else {
            Ok(Self {
                elan_toolchain: tuple.0,
                lean_githash: tuple.1,
                lean_sysroot: tuple.2,
            })
        }
    }

    pub fn lean_sysroot_library_directory(&self) -> PathBuf {
        self.lean_sysroot.join("lib")
    }

    pub fn lean_library_directory(&self) -> PathBuf {
        self.lean_sysroot_library_directory().join("lean")
    }

    pub fn lean_include_directory(&self) -> PathBuf {
        self.lean_sysroot.join("include")
    }

    pub fn lean_clang_include_directory(&self) -> PathBuf {
        self.lean_include_directory().join("clang")
    }

    pub fn lean_lean_include_directory(&self) -> PathBuf {
        self.lean_include_directory().join("lean")
    }

    pub fn lean_header_path(&self) -> PathBuf {
        self.lean_lean_include_directory().join("lean.h")
    }

    fn lean_bin_path(&self) -> PathBuf {
        self.lean_sysroot.join("bin")
    }

    pub fn lean_clang_path(&self) -> PathBuf {
        self.lean_bin_path().join("clang")
    }

    pub fn lean_ar_path(&self) -> PathBuf {
        self.lean_bin_path().join("llvm-ar")
    }

    pub fn export_rustc_env(&self) {
        println!(
            "cargo::rustc-env={}={}",
            Self::ELAN_TOOLCHAIN,
            self.elan_toolchain
        );
        println!(
            "cargo::rustc-env={}={}",
            Self::LEAN_GITHASH,
            self.lean_githash
        );
    }
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

pub fn get_lake_environment<P: AsRef<Path>>(
    lake_package_path: P,
) -> Result<LakeEnv, Box<dyn Error>> {
    let args = [
        OsStr::new("--dir"),
        lake_package_path.as_ref().as_os_str(),
        OsStr::new("env"),
    ];
    let stdout = run_lake_command_and_retrieve_stdout(&args)?;
    LakeEnv::from_posix_env(&stdout)
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

pub fn find_c_files<P: AsRef<Path>>(
    lake_package_path: P,
) -> Result<impl IntoIterator<Item = String>, Box<dyn Error>> {
    let lake_package_path = lake_package_path.as_ref();
    let pattern_path = lake_package_path.join("**/*.c");
    let pattern = pattern_path.to_str().ok_or_else(|| -> Box<dyn Error> {
        format!(
            "Lake package path is not a valid UTF-8 string, \"{}\"",
            lake_package_path.display()
        )
        .into()
    })?;
    let options = MatchOptions {
        case_sensitive: true,
        require_literal_leading_dot: false,
        require_literal_separator: false,
    };
    glob::glob_with(pattern, options)?
        .map(|result| {
            result.map_err(|err| err.into()).and_then(|path| {
                path.to_str()
                    .ok_or_else(|| -> Box<dyn Error> {
                        format!(
                            "C file path is not a valid UTF-8 string, \"{}\"",
                            path.display()
                        )
                        .into()
                    })
                    .map(String::from)
            })
        })
        .collect::<Result<Vec<String>, Box<dyn Error>>>()
}
