# Integrating Lean and Rust <!-- omit from toc -->

This repository contains Rust [crates](https://doc.rust-lang.org/book/ch07-01-packages-and-crates.html#packages-and-crates) for using Lean's runtime and Lean libraries in Rust programs, and provides example programs combining the two languages.

## Table of contents <!-- omit from toc -->

- [Setup](#setup)
  - [Other useful tools](#other-useful-tools)
- [Example](#example)
  - [Lean](#lean)
  - [C](#c)
  - [Unsafe Rust](#unsafe-rust)
  - [Safe Rust](#safe-rust)
- [Credits](#credits)
- [References](#references)

## Setup

1. Install Rust: <https://rust-lang.org/tools/install/>

   This project does not have a well-known set of compatible Rust versions. At the time of writing, the Rust version used was:

   ```text
   cargo 1.90.0 (840b83a10 2025-07-30)
   rustc and rust-std 1.90.0 (1159e78c4 2025-09-14)
   ```

2. Install Lean: <https://lean-lang.org/install/manual/>

   Lean's documentation recommends an [installation through editor plugins](https://lean-lang.org/install/). Editor plugin-guided installation will work as long as the Lean toolchain is added to your shell's `PATH` environment variable. When in doubt, use the manual installation method linked above.

   This project does not have a well-known set of compatible Lean versions. At the time of writing, the Lean version used was:

   ```text
   leanprover/lean4:v4.23.0
   Lean (version 4.23.0, x86_64-unknown-linux-gnu, commit 50aaf682e9b74ab92880292a25c68baa1cc81c87, Release)
   ```

3. Install system dependencies of `bindgen`: <https://rust-lang.github.io/rust-bindgen/requirements.html>

   `bindgen` is used to generate Rust function and type signatures for Lean's C interfaces.

### Other useful tools

1. Tools for analyzing memory management problems, such as [Valgrind](https://valgrind.org/)

## Example

### Lean

We created a small Lean library in [`lean/map_array/MapArray/Basic.lean`](lean/map_array/MapArray/Basic.lean) that we wish to use in a Rust program.

There is a sample Lean program that uses the library in [`lean/map_array_bin/Main.lean`](lean/map_array_bin/Main.lean).

To run the Lean program, run the following commands in a terminal:

```bash
# Navigate into the `lean/map_array_bin` directory
cd lean/map_array_bin
# Build and run the program
lake exe main
```

The program should output

```text
Program start
MapOptions instance: { addend := 2, multiplicand := 3 }
Input array: #[0, 5, 10, 15, 20, 25]
Output array: #[6, 21, 36, 51, 66, 81]
Program end
```

The program creates an array of `6` numbers and passes it to the `map` function from the [Lean `MapArray` library](lean/map_array/MapArray/Basic.lean). `map` requires an options argument, of type `MapOptions`, that contains an addend and a multiplicand. `map` produces an array where each number has been summed with the addend and then multiplied by the multiplicand.

### C

Lean 4 compiles code by generating C code and then compiling the C code with a C compiler. As such, Lean libraries can be used directly by C programs, as explained in Lean's [Foreign Function Interface documentation](https://github.com/leanprover/lean4/blob/master/doc/dev/ffi.md).

Our first step in using Lean libraries from Rust is to learn how to use them from C.

We created a C program with the same functionality as the [Lean program](#lean) in [`c/main.c`](c/main.c).

To run the Lean program, run the following commands.

```bash
cd c
# Run the `test.sh` script
./test.sh
```

> [!NOTE]
> The scripts used to build and run the program were developed on Linux. The scripts may not work in other environments. In contrast, there are no shell scripts for running the Lean and Rust sample programs. It should be possible to run these sample programs in all environments that Lean and Rust support.

The script output should look similar to the following:

```text
+ LAKE=lake
+ ./clean.sh
+ LAKE=lake
+ make run
lake --dir=../lean/map_array build @/MapArray:static
Build completed successfully (6 jobs).
mkdir -p out
cc -o out/main main.c -I $HOME/.elan/toolchains/leanprover--lean4---$VERSION/include \
   ../lean/map_array/.lake/build/lib/libMapArray.a \
   $HOME/.elan/toolchains/leanprover--lean4---$VERSION/lib/lean/libInit.a \
   $HOME/.elan/toolchains/leanprover--lean4---$VERSION/lib/lean/libleanrt.a \
   $HOME/.elan/toolchains/leanprover--lean4---$VERSION/lib/libuv.a \
   $HOME/.elan/toolchains/leanprover--lean4---$VERSION/lib/libgmp.a \
   $HOME/.elan/toolchains/leanprover--lean4---$VERSION/lib/libc++.a \
   $HOME/.elan/toolchains/leanprover--lean4---$VERSION/lib/libc++abi.a \
   -lm
out/main
Program start
MapOptions instance: { addend := 2, multiplicand := 3 }
Populating input array: [ 0, 5, 10, 15, 20, 25, ]
Output array: [ 6, 21, 36, 51, 66, 81, ]
Program end
```

The output includes the commands used to build the program, not only the output from the program itself.

### Unsafe Rust

Rust programmers usually integrate code from other languages in two steps:

1. A low-level [`*-sys` crate](https://doc.rust-lang.org/cargo/reference/build-scripts.html#-sys-packages) links the foreign library and declares the types and functions needed to call into the library from Rust code. The declarations mirror the C interface of the library, and must be used from [`unsafe` Rust code](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html) because the Rust compiler cannot verify whether functions from other languages satisfy Rust's memory safety guarantees.

2. One or more high-level Rust crates depend on the low-level crate and provide idiomatic Rust types and functions that can be used by Rust code without the `unsafe` keyword. Different programmers may have different needs and preferences that lead to different high-level interfaces, but they can all reuse the minimal low-level interface of the library from the `*-sys` crate.

[`rust/map_array_bin/src/bin/low_level.rs`](rust/map_array_bin/src/bin/low_level.rs) is a Rust program that uses our `*-sys` crates for the Lean runtime and for the [Lean `MapArray` library](lean/map_array/MapArray/Basic.lean). It replicates the [C program](#c) and therefore looks very similar. The `unsafe` keyword appears throughout.

To run `low_level.rs`, run the following commands:

```bash
cd rust
cargo run -p map-array-bin --bin low_level
```

The commands should output build output from [Cargo](https://doc.rust-lang.org/cargo/index.html), followed by output from the program itself:

```text
Program start
Lean toolchain version used to build the lean-sys crate: leanprover/lean4:$VERSION
MapOptions instance: { addend := 2, multiplicand := 3 }
Populating input array: [ 0, 5, 10, 15, 20, 25, ]
Output array: [ 6, 21, 36, 51, 66, 81, ]
Program end
```

This low-level program depends on the following Rust crates from this project:

1. [`lean-build`](rust/lean_build) contains utilities for writing the [build scripts](https://doc.rust-lang.org/cargo/reference/build-scripts.html) of `*-sys` crates that use Lean and Lean libraries.

   `lean-build` helps with:

   1. Finding and linking to Lean library files for the Lean runtime and for custom Lean libraries.
   2. Defining Rust equivalents of the types and functions in the C code output by Lean's compiler. We do so using [`bindgen`](https://rust-lang.github.io/rust-bindgen/).
   3. Ensuring that Cargo automatically rebuilds Lean and Rust code whenever there the Lean toolchain version Lean code change.

2. [`lean-sys`](rust/lean_sys) is a low-level crate that links to the Lean runtime using `lean-build`.

3. [`map-array-sys`](rust/map_array_sys) is a low-level crate that links to the [Lean `MapArray` library](lean/map_array/MapArray/Basic.lean) using `lean-build`.

### Safe Rust

[`rust/map_array_bin/src/bin/high_level.rs`](rust/map_array_bin/src/bin/high_level.rs) is a Rust program that uses a high-level Rust interface for the [Lean `MapArray` library](lean/map_array/MapArray/Basic.lean). It is intended to resemble the original [Lean program](#lean), while following Rust style conventions.

`high_level.rs` does not contain the `unsafe` keyword. To emphasize this point, it begins with `#![forbid(unsafe_code)]`, which causes the Rust compiler to raise an error when it encounters `unsafe` code.

To run `high_level.rs`, run the following commands:

```bash
cd rust
cargo run -p map-array-bin --bin high_level
```

The output from the commands should resemble the following:

```text
Program start
Lean toolchain version used to build the lean-sys crate: leanprover/lean4:$VERSION
MapOptions instance: { addend := 2, multiplicand := 3 }
Input array: [0, 5, 10, 15, 20, 25]
Output array: [ 6, 21, 36, 51, 66, 81, ]
Program end
```

This high-level program depends on the following additional Rust crates:

1. [`lean`](rust/lean) provides higher-level abstractions on top of [`lean-sys`](rust/lean_sys).

2. [`map-array`](rust/map_array) provides higher-level abstractions on top of [`map-array-sys`](rust/map_array_sys).

## Credits

The [`rust/lean_build/src/elan_fork/`](rust/lean_build/src/elan_fork) directory contains code adapted from [Elan](https://github.com/leanprover/elan), the Lean version manager. Refer to [`rust/lean_build/src/elan_fork/README.md`](rust/lean_build/src/elan_fork/README.md) for more information.

## References

1. Lean [Foreign Function Interface documentation](https://github.com/leanprover/lean4/blob/master/doc/dev/ffi.md)

2. Lake [Reverse FFI example](https://github.com/leanprover/lean4/tree/14ff08db6f651775ead432d367b6b083878bb0f9/tests/lake/examples/reverse-ffi)

3. [`lean-sys` Rust crate](https://github.com/digama0/lean-sys)

4. [`mimalloc` Rust crate](https://github.com/purpleprotocol/mimalloc_rust)

5. [The bindgen User Guide](https://rust-lang.github.io/rust-bindgen/)

6. [The Rustnomicon](https://doc.rust-lang.org/nomicon/index.html), in particular the [chapter on FFI](https://doc.rust-lang.org/nomicon/ffi.html)
