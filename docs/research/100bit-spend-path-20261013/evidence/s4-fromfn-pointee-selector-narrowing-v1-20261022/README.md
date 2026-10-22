# S4 `from_fn` slice-selector narrowing

This source-only packet preserves two distinct Charon selector experiments
after the Guard-only cut's Aeneas frontend failed on `BuiltinPointee` in
`core::ptr::metadata::metadata` (`metadata.rs:100`). It contains JSON LLBC and
text/JSON receipts, not compiled binaries or Lean objects.

The input workspace and toolchain are the same retained 1.98 isolation setup
as [the preceding Guard extraction](../s4-fromfn-guard-only-extraction-v1-20261022/README.md):
Rust workspace file hashes are in each `source-pins.json`; Charon SHA-256 is
`daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`; Rust is
`1.98.0-nightly (14210df0e 2026-05-31)`, and `core/src/array/mod.rs` SHA-256 is
`fa149bb7f1e856350ccbf94cd402f368ec7f613b8a1d1eeeafffe85b5e75277f`.

`attempt-01-index-opaque` removes only the explicit
`core::slice::index::_::get_unchecked_mut` include. The output still has a
transparent `core::slice::len` (Fun 18), whose body creates a raw pointer,
copies `PtrMetadata`, and calls Foreign Fun 26 `core::ptr::metadata::metadata`.
That function's signature mentions the `BuiltinPointee` associated metadata
type. This directly identifies the remaining source of Aeneas's frontend
error; it was not the now-Foreign index method.

`attempt-02-index-and-len-opaque` also removes the explicit
`core::slice::_::len` include. The resulting LLBC has 49 functions and 17
types, `has_errors=false`, and contains no `Pointee` occurrence or pointer
metadata declaration. `core::slice::len` is Foreign, both inherent and
SliceIndex `get_unchecked_mut` variants are Foreign, while the `Guard` type,
`try_from_fn_erased`, `push_unchecked`, and Guard drop glue remain Transparent;
`MaybeUninit` remains Opaque. This passes the identified Aeneas type-translation
blocker, but is not a source-semantics proof. The separate exact-input Aeneas
feasibility packet reports the next loop-context join failure at
[`s4-fromfn-guard-body-aeneas-v1-20261022`](../s4-fromfn-guard-body-aeneas-v1-20261022/README.md).

Both Charon runs passed fresh admission with `MemoryHigh=1GiB`,
`MemoryMax=2GiB`, and `MemorySwapMax=0`. For attempt 2, the time, Charon, and
Cargo PIDs were all sampled in the same verified cgroup. It exited 0 in
0.404 seconds, with peak process RSS 127072 KiB, zero process swaps, and no
timeout/OOM events. The exact process paths and sampled limits are in its
`receipt.json`.

The packet checker validates every evidence hash, parses both LLBC JSON files,
checks the expected selector/opacity differences, and scans for binary
artifacts. Run:

```sh
python3 check_packet.py
```

The extracted LLBC is from the 1.98 isolation workspace, not the frozen SBF
1.89-dev sysroot; it does not close the original frozen-Std boundary. No Aeneas
translation or Lean theorem is claimed by this extraction packet.
