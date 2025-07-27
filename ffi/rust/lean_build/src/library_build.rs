use std::env;
use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

use bindgen::builder;

use crate::lake;
pub use crate::lake::LakeLibraryDescription;

pub struct OutputFilesConfig<'a> {
    /// The name of the file containing Rust bindings to the Lean library that
    /// will be generated in the build output directory
    ///
    /// The filename extension should be included in the string.
    ///
    /// The full path to the file will be exported as the
    /// `LEAN_LIBRARY_RUST_BINDINGS` environment variable.
    pub library_bindings_filename: &'a str,
}

impl Default for OutputFilesConfig<'static> {
    fn default() -> Self {
        Self {
            library_bindings_filename: "bindings.rs",
        }
    }
}

pub fn build<P: AsRef<Path>, Q: AsRef<Path>>(
    lake_library_description: &LakeLibraryDescription<P, Q>,
    output_files_config: OutputFilesConfig,
) -> Result<(), Box<dyn Error>> {
    let lake_environment = lake::get_lake_environment(&lake_library_description.lake_package_path)?;

    lake::build_and_link_static_lean_library(lake_library_description)?;

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

    let out_dir = PathBuf::from(env::var("OUT_DIR")?);

    let lean_c_files = lake::find_c_files(&lake_library_description.lake_package_path)?;
    let bindings_out_filename = out_dir.join(output_files_config.library_bindings_filename);
    let mut bindings_out_file = File::create(&bindings_out_filename).map_err(|err| {
        format!(
            "failed to create Lean module Rust bindings file \"{}\": {}",
            bindings_out_filename.display(),
            err
        )
    })?;

    for lean_c_file in lean_c_files {
        let file_stem = String::from_utf8(
            Path::new(&lean_c_file)
                .file_stem()
                .ok_or_else(|| format!("no file stem found in \"{lean_c_file}\""))?
                .as_encoded_bytes()
                .to_vec(),
        )
        .unwrap();

        let bindings = builder()
            .clang_args(&["-I", lean_include_directory_str])
            .header(&lean_c_file)
            .blocklist_file(".*\\.h")
            // This function is not defined in user-created Lean modules
            .blocklist_function("initialize_Init")
            .wrap_unsafe_ops(true)
            .wrap_static_fns(false)
            .must_use_type("lean_obj_res")
            .must_use_type("b_lean_obj_res")
            .use_core()
            .merge_extern_blocks(true)
            .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
            .generate()?;

        writeln!(
            &mut bindings_out_file,
            "#[allow(non_snake_case)]
pub mod {file_stem} {{
use lean_sys::*;"
        )?;
        bindings.write(Box::new(&bindings_out_file))?;
        writeln!(&mut bindings_out_file, "}}")?;
    }

    println!(
        "cargo::rustc-env=LEAN_LIBRARY_RUST_BINDINGS={}",
        bindings_out_filename.display()
    );

    Ok(())
}
