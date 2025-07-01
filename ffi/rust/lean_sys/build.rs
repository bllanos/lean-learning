use std::env;
use std::error::Error;
use std::ffi::OsStr;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;

use bindgen::builder;

const INLINE_FUNCTIONS_WRAPPER_NAME: &str = "lean_sys_inline_functions_wrapper";

const LEAN_MODULE_DIRECTORY_NAME: &str = "map_array";

struct LakeEnv {
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

    pub fn lean_header_path(&self) -> PathBuf {
        self.lean_include_directory().join("lean").join("lean.h")
    }

    pub fn elan_toolchain(&self) -> &LeanToolchainVersion {
        &self.elan_toolchain
    }

    pub fn elan_toolchain_directory_path(&self) -> &Path {
        self.lean_sysroot.parent().unwrap()
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

#[derive(PartialEq, Eq)]
enum LeanToolchainVersion {
    Version(String),
    Stable,
}

impl LeanToolchainVersion {
    const STABLE_VERSION: &str = "stable";

    pub fn toolchain_file_path_from_lake_package_path<P: AsRef<Path>>(
        lake_package_path: P,
    ) -> PathBuf {
        lake_package_path.as_ref().join("lean-toolchain")
    }

    pub fn from_toolchain_file<P: AsRef<Path>>(
        toolchain_file_path: P,
    ) -> Result<Self, Box<dyn Error>> {
        let mut toolchain_file = File::open(&toolchain_file_path).map_err(|err| {
            format!(
                "failed to open file \"{}\" to inspect Lean toolchain version: {}",
                toolchain_file_path.as_ref().display(),
                err
            )
        })?;

        let mut version = String::new();
        toolchain_file.read_to_string(&mut version).map_err(|err| {
            format!(
                "failed to read file \"{}\" to inspect Lean toolchain version: {}",
                toolchain_file_path.as_ref().display(),
                err
            )
        })?;

        Self::from_str(&version)
    }
}

impl FromStr for LeanToolchainVersion {
    type Err = Box<dyn Error>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let trimmed_version = s.trim();
        Ok(if trimmed_version == Self::STABLE_VERSION {
            Self::Stable
        } else {
            Self::Version(trimmed_version.into())
        })
    }
}

impl fmt::Display for LeanToolchainVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Stable => f.write_str(Self::STABLE_VERSION),
            Self::Version(str) => f.write_str(&str),
        }
    }
}

fn get_lake_package_path() -> Result<PathBuf, Box<dyn Error>> {
    let manifest_directory = Path::new(env!("CARGO_MANIFEST_DIR"));
    Ok(manifest_directory.parent().ok_or_else(||
        format!(
            "failed to access the parent directory of the Cargo manifest directory \"{}\"",
            manifest_directory.display()
        )
    )?.parent().ok_or_else(|| format!(
        "failed to access the second parent directory of the Cargo manifest directory \"{}\"",
        manifest_directory.display()
    ))?.join(LEAN_MODULE_DIRECTORY_NAME))
}

fn get_lake_environment<P: AsRef<Path>>(lake_package_path: P) -> Result<LakeEnv, Box<dyn Error>> {
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

fn rerun_build_if_lean_version_changes<P: AsRef<Path>>(
    lake_package_path: P,
    lake_env: &LakeEnv,
) -> Result<(), Box<dyn Error>> {
    let toolchain_file_path =
        LeanToolchainVersion::toolchain_file_path_from_lake_package_path(lake_package_path);
    println!("cargo:rerun-if-changed={}", toolchain_file_path.display());

    let lean_toolchain_version = LeanToolchainVersion::from_toolchain_file(&toolchain_file_path)?;
    match lean_toolchain_version {
        LeanToolchainVersion::Stable => {
            let elan_toolchain_directory = lake_env.elan_toolchain_directory_path();
            println!(
                "cargo:warning=specifying \"{}\" as the Lean toolchain version in \"{}\" will slow down Cargo builds because the Elan toolchains directory (\"{}\") must be monitored for changes to detect a Lean toolchain version change",
                LeanToolchainVersion::STABLE_VERSION,
                toolchain_file_path.display(),
                elan_toolchain_directory.display()
            );
            println!(
                "cargo:rerun-if-changed={}",
                elan_toolchain_directory.display()
            );
            Ok(())
        }
        lean_toolchain_version => {
            if &lean_toolchain_version == lake_env.elan_toolchain() {
                Ok(())
            } else {
                Err(format!(
                    "Lean toolchain from \"{}\", \"{}\", does not match the Lean toolchain from the Lake environment, \"{}\"",
                    toolchain_file_path.display(),
                    lean_toolchain_version,
                    lake_env.elan_toolchain()
                ).into())
            }
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let lake_package_path = get_lake_package_path()?;
    let lake_environment = get_lake_environment(&lake_package_path)?;
    let lean_library_directory = lake_environment.lean_library_directory();
    let lean_sysroot_library_directory = lake_environment.lean_sysroot_library_directory();

    lake_environment.export_rustc_env();
    rerun_build_if_lean_version_changes(lake_package_path, &lake_environment)?;

    println!(
        "cargo:rustc-link-search={}",
        lean_library_directory.display()
    );
    println!(
        "cargo:rustc-link-search={}",
        lean_sysroot_library_directory.display()
    );

    println!("cargo:rustc-link-lib=static=Init",);
    println!("cargo:rustc-link-lib=static=leanrt",);
    println!("cargo:rustc-link-lib=static=uv",);
    println!("cargo:rustc-link-lib=static=gmp",);
    println!("cargo:rustc-link-lib=static=c++",);
    println!("cargo:rustc-link-lib=static=c++abi",);
    println!("cargo:rustc-link-lib=dylib=m",);

    let lean_include_directory = lake_environment.lean_include_directory();
    let lean_include_directory_str =
        lean_include_directory
            .to_str()
            .ok_or_else(|| -> Box<dyn Error> {
                format!(
                    "Lean include directory path is not a valid UTF-8 string, \"{}\"",
                    lean_include_directory.display()
                )
                .into()
            })?;

    let lean_header_path = lake_environment.lean_header_path();
    let lean_header_path_str = lean_header_path.to_str().ok_or_else(|| -> Box<dyn Error> {
        format!(
            "Lean header path is not a valid UTF-8 string, \"{}\"",
            lean_header_path.display()
        )
        .into()
    })?;

    let out_dir = PathBuf::from(env::var("OUT_DIR")?);

    let inline_wrapper_functions_out_file =
        out_dir.join(format!("{}.c", INLINE_FUNCTIONS_WRAPPER_NAME));

    let bindings = builder()
        .clang_args(&["-I", lean_include_directory_str])
        .header(lean_header_path_str)
        .wrap_unsafe_ops(true)
        .wrap_static_fns(true)
        .wrap_static_fns_path(&inline_wrapper_functions_out_file)
        // Block functions that produce compilation errors
        .blocklist_function("lean_get_rc_mt_addr")
        .must_use_type("lean_obj_res")
        .must_use_type("b_lean_obj_res")
        .use_core()
        .merge_extern_blocks(true)
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()?;

    let bindings_out_file = out_dir.join("bindings.rs");
    bindings.write_to_file(&bindings_out_file)?;

    println!(
        "cargo::rustc-env=LEAN_RUST_BINDINGS={}",
        bindings_out_file.display()
    );

    cc::Build::new()
        .file(&inline_wrapper_functions_out_file)
        .include(lean_include_directory)
        .compile(INLINE_FUNCTIONS_WRAPPER_NAME);

    Ok(())
}
