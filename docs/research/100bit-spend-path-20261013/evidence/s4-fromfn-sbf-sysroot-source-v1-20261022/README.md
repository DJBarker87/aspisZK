# Frozen SBF sysroot source for `core::array::from_fn`

This packet records the source files present in the exact Solana platform-tools v1.52 Rust sysroot used by the retained SBF build. Read-only NUC inspection found `rustc 1.89.0-dev`, LLVM 20.1.7, with `rustc -Vv` reporting an unknown commit. The source files were copied from that installation's own `lib/rustlib/src/rust/library` tree; no compiler, Charon, Aeneas, or SBF build was run.

The installed `core/src/array/mod.rs` and `core/src/ops/try_trait.rs` have the same full-file SHA-256 hashes as the retained upstream Rust 1.89 comparator files. In the exact sysroot array source, `from_fn` wraps its `FnMut` using `NeverShortCircuit::wrap_mut_1` and calls `try_from_fn`; `try_from_fn` calls `try_from_fn_erased`; the erased helper advances `Guard.initialized`, invokes the generator at that index, and writes with `Guard::push_unchecked`. The checker verifies the whole-file hashes against both retained upstream source snapshots and checks the critical source landmarks.

This establishes source-file availability and body identity with the retained upstream comparator. Since the SBF rustc binary exposes no commit and the producer package does not include its source-build record, this packet does not prove which commit produced the binary. It also does not translate the body into Lean or prove the Aeneas/P6 operational relation. It therefore does not discharge the frozen S4 `from_fn` hypothesis by itself.

Run `python3 -B check_packet.py` from this directory to verify the source snapshots and pins.
