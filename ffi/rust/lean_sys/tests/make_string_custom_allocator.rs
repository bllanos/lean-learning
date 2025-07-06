use std::alloc::{GlobalAlloc, Layout};
use std::ffi::{CStr, CString, c_void};
use std::str::{FromStr, Utf8Error};

use lean_sys::{
    lean_dec_ref, lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_mk_string,
    lean_obj_res, lean_string_cstr, lean_string_push, mi_aligned_alloc, mi_free_size_aligned,
    mi_realloc_aligned, mi_zalloc_aligned,
};

struct MimallocAllocator {}

#[global_allocator]
static ALLOCATOR: MimallocAllocator = MimallocAllocator {};

// Reference:
// <https://github.com/purpleprotocol/mimalloc_rust/blob/000709797d05324e449739ab428180cbe1199712/src/lib.rs>
unsafe impl GlobalAlloc for MimallocAllocator {
    // Required trait methods

    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { mi_aligned_alloc(layout.align(), layout.size()) as *mut u8 }
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe {
            mi_free_size_aligned(ptr as *mut c_void, layout.size(), layout.align());
        }
    }

    // Provided trait methods that mimalloc also supports

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        unsafe { mi_zalloc_aligned(layout.size(), layout.align()) as *mut u8 }
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        unsafe { mi_realloc_aligned(ptr as *mut c_void, new_size, layout.align()) as *mut u8 }
    }
}

/// This test is a version of [`make_string_std()`](./make_string_std.rs) that
/// uses Lean's allocator (assumed to be mimalloc) for dynamic memory allocation
/// in Rust.
#[test]
fn make_string_custom_allocator() -> Result<(), Utf8Error> {
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
