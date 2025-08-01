use std::error::Error;
use std::path::Path;
use std::sync::Arc;

use elan::{Cfg as ElanCfg, Notification, OverrideReason, notify::NotificationLevel};

use crate::toolchain::LeanToolchainVersion;

fn create_elan_cfg() -> Result<ElanCfg, Box<dyn Error>> {
    Ok(ElanCfg::from_env(Arc::new(
        move |n: Notification<'_>| match n.level() {
            NotificationLevel::Verbose => {
                println!("{n}");
            }
            NotificationLevel::Info => {
                println!("{n}");
            }
            NotificationLevel::Warn => {
                println!("cargo:warning={n}");
            }
            NotificationLevel::Error => {
                println!("cargo:error={n}");
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
        OverrideReason::InToolchainDirectory(_) => {
            Err(format!("unexpected toolchain override_reason reason: {override_reason}").into())
        }
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

pub fn rerun_build_if_lean_version_changes<P: AsRef<Path>>(
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
