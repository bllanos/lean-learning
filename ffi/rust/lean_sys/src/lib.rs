#![no_std]
// This warning will hopefully be resolved in a future version of the `bindgen`
// crate
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
include!(env!("LEAN_RUST_BINDINGS"));

pub const ELAN_TOOLCHAIN: &str = env!("ELAN_TOOLCHAIN");
pub const LEAN_GITHASH: &str = env!("LEAN_GITHASH");

unsafe extern "C" {
    pub unsafe fn lean_initialize_runtime_module();
    /// This function replaces [`lean_initialize_runtime_module()`] when code
    /// needs direct or indirect access to the `Lean` package
    pub unsafe fn lean_initialize();
    pub unsafe fn lean_initialize_thread();
    pub unsafe fn lean_finalize_thread();
}
