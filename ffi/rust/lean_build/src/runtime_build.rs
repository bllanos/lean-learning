use std::env;
use std::error::Error;
use std::path::{Path, PathBuf};

use bindgen::builder;

use crate::lake;

pub struct OutputFilesConfig<'a> {
    /// The base of the native library that will be generated to contain functions
    /// that are declared as `inline` in Lean's header files
    ///
    /// For example, `"foo"` will result in `foo.c` and `libfoo.a` in the build
    /// output directory.
    pub inline_functions_library_base_name: &'a str,
    /// The name of the file containing Rust bindings to Lean that will be
    /// generated in the build output directory
    ///
    /// The filename extension should be included in the string.
    pub lean_bindings_filename: &'a str,
    /// The name of the file that can serve as the `lib.rs` file of a Lean sys library
    ///
    /// This file will be output to the build directory with the given name. The
    /// filename extension should be included in the string. It is intended to
    /// be used with `include!()` as follows:
    ///
    /// ```ignore
    /// #![no_std]
    /// #![allow(clippy::missing_safety_doc)]
    /// // These warnings will hopefully be resolved in a future version of the
    /// // `bindgen` crate
    /// #![allow(unsafe_op_in_unsafe_fn)]
    /// #![allow(non_upper_case_globals)]
    /// #![allow(non_camel_case_types)]
    /// #![allow(clippy::ptr_offset_with_cast)]
    /// #![allow(clippy::useless_transmute)]
    /// include!(env!("LEAN_SYS_ROOT_MODULE_INCLUDE"));
    /// ```
    pub lean_sys_root_module_filename: &'a str,
}

impl Default for OutputFilesConfig<'static> {
    fn default() -> Self {
        Self {
            inline_functions_library_base_name: "lean_sys_inline_functions_wrapper",
            lean_bindings_filename: "bindings.rs",
            lean_sys_root_module_filename: "lean_sys_root_module.rs",
        }
    }
}

pub fn build<P: AsRef<Path>>(
    lake_package_path: P,
    output_files_config: OutputFilesConfig,
) -> Result<(), Box<dyn Error>> {
    let lake_environment = lake::get_lake_environment(&lake_package_path)?;
    let lean_library_directory = lake_environment.lean_library_directory();
    let lean_sysroot_library_directory = lake_environment.lean_sysroot_library_directory();

    lake_environment.export_rustc_env();
    crate::elan::rerun_build_if_lean_version_changes(lake_package_path)?;

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

    let inline_wrapper_functions_out_file = out_dir.join(format!(
        "{}.c",
        output_files_config.inline_functions_library_base_name
    ));

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

    let bindings_out_file = out_dir.join(output_files_config.lean_bindings_filename);
    bindings.write_to_file(&bindings_out_file)?;

    println!(
        "cargo::rustc-env=LEAN_RUST_BINDINGS={}",
        bindings_out_file.display()
    );

    cc::Build::new()
        .file(&inline_wrapper_functions_out_file)
        .include(lake_environment.lean_include_directory())
        .include(lake_environment.lean_clang_include_directory())
        .include(lake_environment.lean_lean_include_directory())
        .static_flag(true)
        .compiler(lake_environment.lean_clang_path())
        .archiver(lake_environment.lean_ar_path())
        .compile(output_files_config.inline_functions_library_base_name);

    let lean_sys_root_module_path = out_dir.join(output_files_config.lean_sys_root_module_filename);
    super::rust::create_lean_sys_root_module(lean_sys_root_module_path)?;

    Ok(())
}
