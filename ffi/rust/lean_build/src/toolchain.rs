use std::error::Error;
use std::fmt;
use std::path::Path;
use std::str::FromStr;

use elan::{Cfg as ElanCfg, OverrideReason, Toolchain};
use elan_dist::dist::ToolchainDesc;

#[derive(PartialEq, Eq)]
pub enum LeanToolchainVersion {
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

    pub fn is_floating_version(&self) -> bool {
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
                Some(channel) => FromStr::from_str(channel),
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
            Self::Version(str) => f.write_str(str),
        }
    }
}
