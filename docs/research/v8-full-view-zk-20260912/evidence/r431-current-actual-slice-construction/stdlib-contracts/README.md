# R431 pinned core pointer and slice source contracts

Read-only copies from the same pinned Rust standard-library source tree used by R429:
`/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src`.
Exact full source files are under `source/`, and copied-file hashes, paths, and relevant ranges are in `inventory.json` and `SHA256SUMS`.

The inventory records source-level contracts and delegation only. `NonNull::add` delegates to raw pointer `offset`; `NonNull::offset_from_unsigned` delegates to the raw-pointer wrapper; `NonNull::as_ptr` transmutes the transparent wrapper; `NonNull` equality compares its raw pointers. The raw pointer wrapper documents and checks preconditions before calling the respective intrinsic. `slice::Iter::new` is an inline constructor called by the inline `[T]::iter` wrapper. The iterator's generated `next` body branches on `T::IS_ZST`, checks empty, then uses `unchecked_sub(1)` for ZST length or pointer equality and `NonNull::add(1)` for non-ZST, before producing the current reference.

No Rust compiler/build was run. This inventory does not establish any premise for the concrete selected iterator, nor a Rust-to-LLBC/Aeneas/Lean correspondence or pointer/aliasing semantics theorem. Safety documentation is transcribed as documentation from the pinned source, not discharged here.
