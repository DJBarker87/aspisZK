# Current `WideExact::to_le_bytes` source-cut extraction

This packet extracts the unchanged current `crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes` body through a tiny typed entrypoint. The method itself was copied byte-for-byte; the wrapper only exposes the private crate method as a Charon root. The exact source files and method span are checked by `check-source.py`.

The isolated offline Cargo typecheck and bounded NUC Charon/Aeneas runs succeeded. Charon retained the real method and its iterator loop in the LLBC (`WideExactToBytes.llbc`, SHA-256 `5e13162590786bb23a9ea282a1f43109ce1cbffbff4247c6cab1fdf7baf401a0`, intentionally not copied into this source-only packet). Aeneas emitted `to_limbs`, the loop body/loop, `to_le_bytes`, and the public entry. This packet establishes extraction only; it has no Lean refinement theorem and makes no claim that the Rust standard-library iterator/copy operations have been proved.

`FunsExternal_Template.lean` and `TypesExternal_Template.lean` are retained as diagnostics only. The external template contains axioms for array/slice iterators and mutable slice operations, so it is not an accepted proof dependency and must not be imported into a standard-axiom proof. The next proof step must reuse or establish checked semantics for `ChunksExactMut`, `Zip`, array `IntoIter`, `U32.to_le_bytes`, and `Slice.copy_from_slice`, then connect the resulting bytes to the existing strict wide-byte codec.

The NUC scopes used fresh admission against the host collector and ran with `MemoryHigh=2GiB`, `MemoryMax=4GiB`, `MemorySwapMax=0`. Charon: exit 0, 1.404 s, process peak RSS 214,408 KiB, cgroup peak 114,143,232 bytes, swap 0. Aeneas: exit 0, 0.604 s, process peak RSS 79,376 KiB, cgroup peak 68,784,128 bytes, swap 0. The two admission, reservation, receipt, command, time, and log files are preserved under `attempt/`.

The Cargo preflight was a tiny offline typecheck and did not collect RSS/swap telemetry; this is recorded as such in `cargo-preflight-receipt.json`. No production Rust file was edited.
