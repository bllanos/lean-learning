use std::convert::Infallible;
use std::ffi::{CStr, CString};
use std::str::FromStr;
use std::thread;

use lean::{MimallocAllocator, Minimal, NoModules, Runtime};
use lean_sys::{lean_dec_ref, lean_mk_string, lean_obj_res, lean_string_cstr, lean_string_push};

#[global_allocator]
static ALLOCATOR: MimallocAllocator = MimallocAllocator {};

#[test]
fn make_string() {
    lean::run_in_lean_runtime_with_default_error_handler(
        |runtime: &Runtime<Minimal, NoModules>| {
            let initial_string = String::from("Hello, world");
            let new_char = b'!';
            let initial_cstring = CString::from_str(&initial_string).unwrap();

            thread::scope(|scope| {
                lean::run_in_custom_scoped_thread_with_lean_runtime(
                    runtime,
                    thread::Builder::new().name("test_lean_thread".into()),
                    scope,
                    |_| {
                        let initial_string_ptr = initial_cstring.as_ptr();
                        let longer_lean_string: lean_obj_res;
                        let final_cstring: &CStr;

                        unsafe {
                            let lean_string = lean_mk_string(initial_string_ptr);
                            longer_lean_string = lean_string_push(lean_string, new_char as u32);
                            let longer_lean_cstring = lean_string_cstr(longer_lean_string);
                            final_cstring = CStr::from_ptr(longer_lean_cstring);
                        }

                        let final_string = final_cstring.to_str().unwrap();
                        let mut expected_string = initial_string.clone();
                        expected_string.push(new_char as char);
                        assert_eq!(final_string, expected_string);

                        unsafe {
                            lean_dec_ref(longer_lean_string);
                        }
                    },
                )
                .unwrap();
            });
            Ok::<_, Infallible>(())
        },
    )
    .unwrap();
}
