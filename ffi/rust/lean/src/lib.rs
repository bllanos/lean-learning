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

/// A set of features that are available in the Lean runtime
///
/// # Safety
///
/// Implementations of this trait must guarantee that the Lean runtime is
/// properly initialized.
pub unsafe trait RuntimeComponents {
    /// Initialize the Lean runtime
    ///
    /// # Safety
    ///
    /// Callers must ensure that the Lean runtime is initialized at most once.
    unsafe fn initialize_runtime();
}
