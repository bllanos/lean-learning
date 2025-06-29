use std::ffi::{CStr, CString};
use std::str::{FromStr, Utf8Error};

use lean_sys::{
    lean_dec_ref, lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_mk_string,
    lean_obj_res, lean_string_cstr, lean_string_push,
};

/// This test demonstrates that both Rust and Lean can use dynamic memory
/// allocation with their respective default allocators in the same program. In
/// practice, it is probably better to use `#![no_std]` and only have one
/// allocator in the program, by exclusively using Lean objects, allocated using
/// Lean's allocation functions for specific types of Lean objects. This
/// approach is used in [`make_string_no_std()`](./make_string_no_std.rs).
///
/// Rather than use Lean's allocation functions for specific types of Lean
/// objects, one could program using Rust objects but use Lean's allocator to
/// allocate them. Using Lean's allocator with Rust's standard library objects
/// looks fragile, however, because Rust code needs to be aware of Lean's
/// build-time memory allocation configuration, specifically the `LEAN_MIMALLOC`
/// and `LEAN_SMALL_ALLOCATOR` options. An example of using Lean's allocator as
/// Rust's global allocator is shown at
/// <https://github.com/digama0/lean-sys/blob/dd7ff0cfa4a70ad8d1aecc7f8cb6ced776664c11/src/alloc.rs>.
#[test]
fn make_string_std() -> Result<(), Utf8Error> {
    unsafe {
        lean_initialize_runtime_module();
        lean_io_mark_end_initialization();
    }

    let initial_string = String::from("Hello, world");
    let new_char = b'!';
    let initial_cstring = CString::from_str(&initial_string).unwrap();
    let initial_string_ptr = initial_cstring.as_ptr();

    let longer_lean_string: lean_obj_res;
    let final_cstring: &CStr;

    unsafe {
        let lean_string = lean_mk_string(initial_string_ptr);
        longer_lean_string = lean_string_push(lean_string, new_char as u32);
        let longer_lean_cstring = lean_string_cstr(longer_lean_string);
        final_cstring = CStr::from_ptr(longer_lean_cstring);
    }

    let final_string = final_cstring.to_str()?;
    let mut expected_string = initial_string.clone();
    expected_string.push(new_char as char);
    assert_eq!(final_string, expected_string);

    unsafe {
        lean_dec_ref(longer_lean_string);
    }

    Ok(())
}
