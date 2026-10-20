# Rust `array::IntoIter` source boundary

This note records the exact Rust library boundary used by the generated Query31 owner. It is a source inspection and mapping record, not a Lean proof that unsafe core methods refine the explicit iterator model.

## Toolchain/source identity

- The extraction input manifest pins `toolchain = nightly-2026-06-01`; command plan and Charon/Aeneas environment use `RUSTUP_TOOLCHAIN=nightly-2026-06-01`.
- On the NUC, the source was read from that same rustup installation: `/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src`.
- That toolchain's rustc reports `1.98.0-nightly (14210df0e 2026-05-31)`, commit hash `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, host `x86_64-unknown-linux-gnu`, LLVM `22.1.6`.
- The rust-src tree has no `.git` directory, so the file hashes below, rustup path, and rustc identity are retained; no independent rust-src Git commit is claimed.

## Relevant source operations

`core/array/iter.rs` (SHA-256 `570b98951edb1bf47932c2de58dc4d3f38f34d37b3dffeac2fe80572dc0475cb`):

- `IntoIterator for [T; N]::into_iter`, lines 56–79, transmutes the consumed array to `[MaybeUninit<T>; N]`, constructs `InnerSized::new_unchecked(IndexRange::zero_to(N), data)`, and wraps it in `IntoIter`.
- `Iterator for IntoIter<T, N>::next`, lines 242–245, delegates to `self.unsize_mut().next()`.

`core/array/iter/iter_inner.rs` (SHA-256 `6906e8e1e1956d415a9058df036e2a28fe0938dbae0b2c499a5889d8b983c4c1`):

- `PolymorphicIter::next`, lines 213–225, calls `self.alive.next()`, then reads `self.data.get_unchecked(idx).assume_init_read()`.
- Its comments state that the `alive` range denotes initialized, not-yet-yielded values; the yielded element becomes dead and must no longer be touched.

Supporting implementation files are snapshotted too:

- `core/ops/index_range.rs`, SHA-256 `be7f1a663156319aa4762288c44b726338276f0bcb1c36a5ced5003d329deb8f`, defines `zero_to` as start 0/end N and `next`/`next_unchecked` as returning the previous start while incrementing it.
- `core/mem/maybe_uninit.rs`, SHA-256 `cd1152779de3a6bc96b29997e8a95d3beb9ff1018f99223b429ed0df66baa8ef`, defines `assume_init_read` as a pointer read under the caller's initialized-value safety obligation.

## Exact remaining correspondence

The Lean proof currently models these calls by explicit `IntoIter` operation parameters. Generated Aeneas output declares `Array.into_iter` and `IntoIter.next` in `FunsExternal_Template.lean`; it does not emit either implementation body. The generated `QueryScan.scan` is source-pinned to call `query_words`, then `Array.into_iter`, then `scan_loop`, whose loop body calls `IntoIter.next`.

The Rust source supports the intended front-to-back order by construction, but a proof still needs to establish the unsafe representation invariant and `MaybeUninit` read relation, and then connect those source operations to the two generated external signatures. This packet does not discharge that library-body correspondence. The accepted Lean sources import neither `TypesExternal` nor `FunsExternal` and contain no iterator axioms.
