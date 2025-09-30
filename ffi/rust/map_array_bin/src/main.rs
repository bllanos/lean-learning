#![forbid(unsafe_code)]

use lean_sys::ELAN_TOOLCHAIN;

fn main() {
    println!(
        "Lean toolchain version used to build the lean-sys crate: {}",
        ELAN_TOOLCHAIN
    );
}
