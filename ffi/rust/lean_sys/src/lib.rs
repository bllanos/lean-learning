#![no_std]
#![allow(clippy::missing_safety_doc)]
// These warnings will hopefully be resolved in a future version of the
// `bindgen` crate
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::ptr_offset_with_cast)]
#![allow(clippy::useless_transmute)]
include!(env!("LEAN_SYS_ROOT_MODULE_INCLUDE"));
