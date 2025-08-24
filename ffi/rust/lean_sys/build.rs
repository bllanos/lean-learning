use std::env;
use std::error::Error;
use std::path::{Path, PathBuf};

use lean_build::LakePackageDescription;

const LEAN_MODULE_DIRECTORY_NAME: &str = "map_array";

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

fn main() -> Result<(), Box<dyn Error>> {
    let lake_package_path = get_lake_package_path()?;
    lean_build::runtime_build::build(
        LakePackageDescription {
            lake_package_path,
            lake_executable_path: None::<PathBuf>,
        },
        Default::default(),
    )
}
