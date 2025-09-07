use std::error::Error;
use std::ffi::{CStr, CString};
use std::fmt;
use std::marker::PhantomData;

use lean_sys::{
    b_lean_obj_arg, lean_box, lean_dec, lean_inc, lean_io_error_to_string, lean_io_mk_world,
    lean_io_result_get_error, lean_io_result_is_ok, lean_io_result_mk_ok, lean_obj_arg,
    lean_obj_res, lean_object, lean_string_cstr,
};

use crate::{Modules, Runtime, RuntimeComponents, util::NonSendNonSync};

pub enum NoModules {}

unsafe impl Modules for NoModules {
    unsafe fn initialize_modules(_builtin: u8, _lean_io_world: lean_obj_arg) -> lean_obj_res {
        unsafe { lean_io_result_mk_ok(lean_box(0)) }
    }
}

pub struct ModulesInitializer<R: RuntimeComponents, M: Modules> {
    runtime_components: PhantomData<R>,
    modules_initializer: PhantomData<M>,
    non_send_non_sync: NonSendNonSync,
}

impl<R: RuntimeComponents, M: Modules> ModulesInitializer<R, M> {
    fn initialize_fields() -> Self {
        Self {
            runtime_components: PhantomData,
            modules_initializer: PhantomData,
            non_send_non_sync: PhantomData,
        }
    }

    pub fn new() -> Result<Self, lean_obj_res> {
        let res: *mut lean_object;
        // Use same default as for Lean executables
        // See <https://github.com/leanprover/lean4/blob/master/doc/dev/ffi.md#initialization>
        let builtin: u8 = 1;

        unsafe {
            res = M::initialize_modules(builtin, lean_io_mk_world());
            if lean_io_result_is_ok(res) {
                lean_dec(res);
                Ok(Self::initialize_fields())
            } else {
                Err(res)
            }
        }
    }

    pub fn mark_end_initialization(self) -> Runtime<R, M> {
        unsafe {
            R::mark_end_initialization();
        }
        Runtime::new()
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct LeanIoError(pub CString);

impl fmt::Display for LeanIoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0.to_string_lossy())
    }
}

impl Error for LeanIoError {}

impl LeanIoError {
    /// Create an instance from a Lean IO error
    ///
    /// # Safety
    ///
    /// Callers must ensure that `lean_io_error` points to a valid error object
    pub unsafe fn from_lean_io_error(lean_io_error: b_lean_obj_arg) -> Self {
        let owned_string: CString;
        unsafe {
            lean_inc(lean_io_error);
            let lean_string = lean_io_error_to_string(lean_io_error);
            let lean_cstring = lean_string_cstr(lean_string);
            owned_string = CStr::from_ptr(lean_cstring).to_owned();
            lean_dec(lean_string);
        }
        Self(owned_string)
    }

    /// Create an instance from a Lean IO error contained in a Lean IO result
    ///
    /// # Safety
    ///
    /// Callers must ensure that `lean_io_result` points to a valid result
    /// object and that it is an error variant
    pub unsafe fn from_lean_io_result(lean_io_result: b_lean_obj_arg) -> Self {
        unsafe {
            let lean_io_error = lean_io_result_get_error(lean_io_result);
            Self::from_lean_io_error(lean_io_error)
        }
    }
}
