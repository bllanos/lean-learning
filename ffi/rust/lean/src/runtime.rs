use std::error::Error;
use std::sync::Once;

mod types;

use crate::RuntimeComponents;
pub use types::{InitializingRuntime, LeanPackage, Minimal, Runtime};

static ONCE_INITIALIZATION_GUARD: Once = Once::new();

pub fn run_in_lean_runtime<
    C: RuntimeComponents,
    T,
    E: Error,
    Init: FnOnce(&InitializingRuntime<C>) -> Result<(), E>,
    Run: FnOnce(&Runtime<C>) -> Result<T, E>,
>(
    init: Init,
    run: Run,
) -> Result<T, E> {
    let mut result = None;
    ONCE_INITIALIZATION_GUARD.call_once(|| {
        let initializing_runtime = InitializingRuntime::new();
        result = match init(&initializing_runtime) {
            Ok(()) => {
                let runtime = initializing_runtime.finish_initialization();
                match run(&runtime) {
                    Ok(value) => Some(Ok(value)),
                    Err(e) => Some(Err(e)),
                }
            }
            Err(e) => Some(Err(e)),
        };
    });
    result.unwrap()
}
