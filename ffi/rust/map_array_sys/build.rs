use std::env;
use std::error::Error;
use std::path::{Path, PathBuf};

use lean_build::library_build::LakeLibraryDescription;

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
    lean_build::library_build::build(
        &LakeLibraryDescription {
            lake_package_path,
            target_name: "MapArray",
            source_directory: None::<PathBuf>,
        },
        Default::default(),
    )
}
