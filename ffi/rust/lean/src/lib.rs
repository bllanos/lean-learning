pub use lean_sys::ELAN_TOOLCHAIN;
pub use lean_sys::LEAN_GITHASH;

mod alloc;
mod runtime;
mod thread;

pub use alloc::MimallocAllocator;
pub use runtime::{InitializingRuntime, LeanPackage, Minimal, Runtime, run_in_lean_runtime};
pub use thread::{
    run_in_custom_scoped_thread_with_lean_runtime, run_in_custom_thread_with_lean_runtime,
    run_in_thread_with_lean_runtime,
};

pub unsafe trait RuntimeComponents {
    unsafe fn initialize_runtime();
}
