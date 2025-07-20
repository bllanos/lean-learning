#![no_std]
// This warning will hopefully be resolved in a future version of the `bindgen`
// crate
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
include!(env!("LEAN_SYS_ROOT_MODULE_INCLUDE"));
