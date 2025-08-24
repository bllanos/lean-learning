use std::error::Error;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};

use super::{LakePackageDescription, display_slice};

pub struct LakeEnv {
    elan_toolchain: String,
    lean_githash: String,
    lean_sysroot: PathBuf,
}

impl LakeEnv {
    const ELAN_TOOLCHAIN: &str = "ELAN_TOOLCHAIN";
    const LEAN_GITHASH: &str = "LEAN_GITHASH";
    const LEAN_SYSROOT: &str = "LEAN_SYSROOT";

    fn from_posix_env(env: &[u8]) -> Result<Self, Box<dyn Error>> {
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

pub fn get_lake_environment<P: AsRef<Path>, Q: AsRef<OsStr>>(
    lake_package_description: &LakePackageDescription<P, Q>,
) -> Result<LakeEnv, Box<dyn Error>> {
    let args = [
        OsStr::new("--dir"),
        lake_package_description.get_lake_package_path().as_os_str(),
        OsStr::new("env"),
    ];
    let stdout = super::run_lake_command_and_retrieve_stdout(
        lake_package_description.get_lake_executable_path(),
        &args,
    )?;
    LakeEnv::from_posix_env(&stdout)
}
