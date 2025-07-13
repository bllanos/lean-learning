use std::thread::{Builder, JoinHandle, Scope, ScopedJoinHandle};

use lean_sys::{lean_finalize_thread, lean_initialize_thread};

use crate::{Runtime, RuntimeComponents};

fn run_lean_thread<C: RuntimeComponents, T, Run: FnOnce(&Runtime<C>) -> T>(run: Run) -> T {
    unsafe {
        lean_initialize_thread();
    }
    let runtime = Runtime::new();
    let output = run(&runtime);
    unsafe {
        lean_finalize_thread();
    }
    output
}

pub fn run_in_thread_with_lean_runtime<
    C: RuntimeComponents,
    T: Send + 'static,
    Run: FnOnce(&Runtime<C>) -> T + Send + 'static,
>(
    _runtime: &Runtime<C>,
    run: Run,
) -> JoinHandle<T> {
    std::thread::spawn(move || run_lean_thread(run))
}

pub fn run_in_custom_thread_with_lean_runtime<
    C: RuntimeComponents,
    T: Send + 'static,
    Run: FnOnce(&Runtime<C>) -> T + Send + 'static,
>(
    _runtime: &Runtime<C>,
    builder: Builder,
    run: Run,
) -> std::io::Result<JoinHandle<T>> {
    builder.spawn(move || run_lean_thread(run))
}

pub fn run_in_custom_scoped_thread_with_lean_runtime<
    'scope,
    'env,
    C: RuntimeComponents,
    T: Send + 'scope,
    Run: FnOnce(&Runtime<C>) -> T + Send + 'scope,
>(
    _runtime: &Runtime<C>,
    builder: Builder,
    scope: &'scope Scope<'scope, 'env>,
    run: Run,
) -> std::io::Result<ScopedJoinHandle<'scope, T>> {
    builder.spawn_scoped(scope, move || run_lean_thread(run))
}
