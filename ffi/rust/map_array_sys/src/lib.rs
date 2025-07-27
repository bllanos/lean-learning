#![no_std]
// These warnings will hopefully be resolved in a future version of the
// `bindgen` crate
#![allow(non_upper_case_globals)]
include!(env!("LEAN_LIBRARY_RUST_BINDINGS"));
