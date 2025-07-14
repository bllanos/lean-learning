use std::error::Error;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;

use crate::toolchain::LeanToolchainVersion;

pub struct LakeEnv {
    elan_toolchain: LeanToolchainVersion,
    lean_githash: String,
    lean_sysroot: PathBuf,
}

impl LakeEnv {
    const ELAN_TOOLCHAIN: &str = "ELAN_TOOLCHAIN";
    const LEAN_GITHASH: &str = "LEAN_GITHASH";
    const LEAN_SYSROOT: &str = "LEAN_SYSROOT";

    pub fn from_posix_env(env: &[u8]) -> Result<Self, Box<dyn Error>> {
        let tuple = env.split(|c| c.is_ascii_control()).try_fold(
            (
                None,
                String::new(),
                PathBuf::new(),
            ),
            |accumulator, slice| -> Result<(Option<LeanToolchainVersion>, String, PathBuf), Box<dyn Error>> {
                let mut parts = slice.splitn(2, |c| *c == b'=');
                let var = parts.next().ok_or_else(|| {
                    format!(
                        "no variable name in environment line \"{}\"",
                        str::from_utf8(slice).unwrap_or("[Non-UTF8]")
                    )
                })?;
                match parts.next() {
                    None => Ok(accumulator),
                    Some(value) => {
                        let var_str = str::from_utf8(var)?;
                        match var_str {
                            Self::ELAN_TOOLCHAIN => {
                                let value_str = str::from_utf8(value)?;
                                if accumulator.0.is_none() {
                                    Ok((
                                        Some(FromStr::from_str(value_str)?),
                                        accumulator.1,
                                        accumulator.2,
                                    ))
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
                                    Ok((
                                        accumulator.0,
                                        String::from(value_str),
                                        accumulator.2,
                                    ))
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
                                    Ok((
                                        accumulator.0,
                                        accumulator.1,
                                        PathBuf::from(value_str),
                                    ))
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
        match tuple.0 {
            Some(elan_toolchain) => {
                if tuple.1.is_empty() {
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
                        elan_toolchain,
                        lean_githash: tuple.1,
                        lean_sysroot: tuple.2,
                    })
                }
            }
            None => Err(format!(
                "missing {} variable in environment string",
                Self::ELAN_TOOLCHAIN
            )
            .into()),
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

pub fn get_lake_environment<P: AsRef<Path>>(
    lake_package_path: P,
) -> Result<LakeEnv, Box<dyn Error>> {
    let args = [
        OsStr::new("--dir"),
        lake_package_path.as_ref().as_os_str(),
        OsStr::new("env"),
    ];
    let output = Command::new("lake").args(args).output()?;
    if output.status.success() {
        LakeEnv::from_posix_env(&output.stdout)
    } else {
        Err(format!("Lake invocation with arguments {:?} failed", args).into())
    }
}
