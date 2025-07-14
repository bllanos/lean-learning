use std::env;
use std::error::Error;
use std::path::{Path, PathBuf};

use bindgen::builder;

use crate::lake;

const INLINE_FUNCTIONS_WRAPPER_NAME: &str = "lean_sys_inline_functions_wrapper";

pub fn build<P: AsRef<Path>>(lake_package_path: P) -> Result<(), Box<dyn Error>> {
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
        .include(lake_environment.lean_include_directory())
        .include(lake_environment.lean_clang_include_directory())
        .include(lake_environment.lean_lean_include_directory())
        .static_flag(true)
        .compiler(lake_environment.lean_clang_path())
        .archiver(lake_environment.lean_ar_path())
        .compile(INLINE_FUNCTIONS_WRAPPER_NAME);

    Ok(())
}
