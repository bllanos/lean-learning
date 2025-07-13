use std::marker::PhantomData;

use lean_sys::{lean_initialize, lean_initialize_runtime_module, lean_io_mark_end_initialization};

use crate::RuntimeComponents;

pub struct Minimal {}

unsafe impl RuntimeComponents for Minimal {
    unsafe fn initialize_runtime() {
        unsafe {
            lean_initialize_runtime_module();
        }
    }
}

pub struct LeanPackage {}

unsafe impl RuntimeComponents for LeanPackage {
    unsafe fn initialize_runtime() {
        unsafe {
            lean_initialize();
        }
    }
}

// Reference:
// <https://stackoverflow.com/questions/62713667/how-to-implement-send-or-sync-for-a-type>
// This is a workaround until [negative
// impls](https://github.com/rust-lang/rust/issues/68318) are stable.
type NonSendNonSync = PhantomData<*const ()>;

pub struct InitializingRuntime<T: RuntimeComponents> {
    runtime_components: PhantomData<T>,
    non_send_non_sync: NonSendNonSync,
}

impl<T: RuntimeComponents> InitializingRuntime<T> {
    fn initialize_fields() -> Self {
        Self {
            runtime_components: PhantomData,
            non_send_non_sync: PhantomData,
        }
    }

    pub(super) fn new() -> Self {
        unsafe {
            T::initialize_runtime();
        }
        Self::initialize_fields()
    }

    pub(super) fn finish_initialization(self) -> Runtime<T> {
        unsafe {
            lean_io_mark_end_initialization();
        }
        Runtime::new()
    }
}

pub struct Runtime<T: RuntimeComponents> {
    runtime_components: PhantomData<T>,
    non_send_non_sync: NonSendNonSync,
}

impl<T: RuntimeComponents> Runtime<T> {
    pub(crate) fn new() -> Self {
        Self {
            runtime_components: PhantomData,
            non_send_non_sync: PhantomData,
        }
    }
}
