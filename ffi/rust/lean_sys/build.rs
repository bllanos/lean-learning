use std::env;
use std::error::Error;
use std::ffi::OsStr;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;
use std::sync::Arc;

use bindgen::builder;
use elan::{Cfg as ElanCfg, Notification, OverrideReason, Toolchain, notify::NotificationLevel};
use elan_dist::dist::ToolchainDesc;

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

fn create_elan_cfg() -> Result<ElanCfg, Box<dyn Error>> {
    Ok(ElanCfg::from_env(Arc::new(
        move |n: Notification<'_>| match n.level() {
            NotificationLevel::Verbose => {
                println!("{}", n);
            }
            NotificationLevel::Info => {
                println!("{}", n);
            }
            NotificationLevel::Warn => {
                println!("cargo:warning={}", n);
            }
            NotificationLevel::Error => {
                println!("cargo:error={}", n);
            }
        },
    ))?)
}

fn rerun_build_if_elan_environment_variables_change() {
    println!("cargo:rerun-if-env-changed=ELAN_TOOLCHAIN");
}

fn rerun_build_if_elan_settings_change(elan_cfg: &ElanCfg) {
    println!(
        "cargo:rerun-if-changed={}",
        elan_cfg.elan_dir.join("settings.toml").display()
    );
}

fn rerun_build_if_lean_toolchain_override_changes(
    elan_cfg: &ElanCfg,
    override_reason: &OverrideReason,
) -> Result<(), Box<dyn Error>> {
    match override_reason {
        OverrideReason::Environment => {
            rerun_build_if_elan_environment_variables_change();
            Ok(())
        }
        OverrideReason::InToolchainDirectory(_) => Err(format!(
            "unexpected toolchain override_reason reason: {}",
            override_reason
        )
        .into()),
        OverrideReason::LeanpkgFile(path) => {
            println!("cargo:rerun-if-changed={}", path.display());
            Ok(())
        }
        OverrideReason::OverrideDB(_) => {
            rerun_build_if_elan_settings_change(elan_cfg);
            Ok(())
        }
        OverrideReason::ToolchainFile(path) => {
            println!("cargo:rerun-if-changed={}", path.display());
            Ok(())
        }
    }
}

#[derive(PartialEq, Eq)]
enum LeanToolchainVersion {
    Version(String),
    Nightly,
    Beta,
    Stable,
}

impl LeanToolchainVersion {
    const NIGHTLY_VERSION: &str = "nightly";
    const BETA_VERSION: &str = "beta";
    const STABLE_VERSION: &str = "stable";

    pub fn from_lake_package_path<P: AsRef<Path>>(
        elan_cfg: &ElanCfg,
        lake_package_path: P,
    ) -> Result<(Self, Option<OverrideReason>), Box<dyn Error>> {
        let (toolchain, override_reason) =
            elan_cfg.toolchain_for_dir(lake_package_path.as_ref())?;
        Ok((toolchain.try_into()?, override_reason))
    }

    fn is_floating_version(&self) -> bool {
        !matches!(self, Self::Version(_))
    }
}

impl FromStr for LeanToolchainVersion {
    type Err = Box<dyn Error>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let trimmed_version = s.trim();
        Ok(match trimmed_version {
            Self::NIGHTLY_VERSION => Self::Nightly,
            Self::BETA_VERSION => Self::Beta,
            Self::STABLE_VERSION => Self::Stable,
            specific_version => Self::Version(specific_version.into()),
        })
    }
}

impl<'a> TryFrom<Toolchain<'a>> for LeanToolchainVersion {
    type Error = Box<dyn Error>;

    fn try_from(toolchain: Toolchain<'a>) -> Result<Self, Self::Error> {
        let desc = toolchain.desc;
        match desc {
            ToolchainDesc::Local { name } => Ok(Self::Version(name)),
            ToolchainDesc::Remote {
                ref from_channel, ..
            } => match from_channel {
                Some(channel) => FromStr::from_str(&channel),
                None => FromStr::from_str(&desc.to_string()),
            },
        }
    }
}

impl fmt::Display for LeanToolchainVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nightly => f.write_str(Self::NIGHTLY_VERSION),
            Self::Beta => f.write_str(Self::BETA_VERSION),
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
) -> Result<(), Box<dyn Error>> {
    rerun_build_if_elan_environment_variables_change();
    let elan_cfg = create_elan_cfg()?;
    rerun_build_if_elan_settings_change(&elan_cfg);
    let (lean_toolchain_version, override_reason) =
        LeanToolchainVersion::from_lake_package_path(&elan_cfg, &lake_package_path)?;
    if let Some(override_reason) = override_reason {
        rerun_build_if_lean_toolchain_override_changes(&elan_cfg, &override_reason)?;
    }

    if lean_toolchain_version.is_floating_version() {
        let elan_toolchain_directory = &elan_cfg.toolchains_dir;
        println!(
            "cargo:warning=specifying \"{}\" as the Lean toolchain version will slow down Cargo builds because the entire Elan toolchains directory (\"{}\") must be monitored for changes to detect a Lean toolchain version change",
            lean_toolchain_version,
            elan_toolchain_directory.display()
        );
        println!(
            "cargo:rerun-if-changed={}",
            elan_toolchain_directory.display()
        );
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let lake_package_path = get_lake_package_path()?;
    let lake_environment = get_lake_environment(&lake_package_path)?;
    let lean_library_directory = lake_environment.lean_library_directory();
    let lean_sysroot_library_directory = lake_environment.lean_sysroot_library_directory();

    lake_environment.export_rustc_env();
    rerun_build_if_lean_version_changes(lake_package_path)?;

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
