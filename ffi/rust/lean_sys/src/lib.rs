// This warning will hopefully be resolved in a future version of the `bindgen`
// crate
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
include!(env!("LEAN_RUST_BINDINGS"));

unsafe extern "C" {
    pub unsafe fn lean_initialize_runtime_module();
    /// This would replace `lean_initialize_runtime_module()` if the code accesses the `Lean` package
    pub unsafe fn lean_initialize();
}
