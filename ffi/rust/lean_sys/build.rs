use std::env;
use std::error::Error;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

use bindgen::builder;

const INLINE_FUNCTIONS_WRAPPER_NAME: &str = "lean_sys_inline_functions_wrapper";

const LEAN_MODULE_DIRECTORY_NAME: &str = "map_array";

struct LakeEnv {
    lean_githash: String,
    lean_sysroot: PathBuf,
}

impl LakeEnv {
    const LEAN_GITHASH: &str = "LEAN_GITHASH";
    const LEAN_SYSROOT: &str = "LEAN_SYSROOT";

    pub fn from_posix_env(env: &[u8]) -> Result<Self, Box<dyn Error>> {
        env.split(|c| c.is_ascii_control()).try_fold(
            Self {
                lean_githash: String::new(),
                lean_sysroot: PathBuf::new(),
            },
            |accumulator, slice| -> Result<Self, Box<dyn Error>> {
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
                            Self::LEAN_GITHASH => {
                                let value_str = str::from_utf8(value)?;
                                if accumulator.lean_githash.is_empty() {
                                    Ok(Self {
                                        lean_githash: String::from(value_str),
                                        ..accumulator
                                    })
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
                                if accumulator.lean_sysroot.as_os_str().is_empty() {
                                    Ok(Self {
                                        lean_sysroot: PathBuf::from(value_str),
                                        ..accumulator
                                    })
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
        )
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

fn main() -> Result<(), Box<dyn Error>> {
    let lake_package_path = get_lake_package_path()?;
    let lake_environment = get_lake_environment(&lake_package_path)?;
    let lean_library_directory = lake_environment.lean_library_directory();
    let lean_sysroot_library_directory = lake_environment.lean_sysroot_library_directory();

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
