# S9 actual `WideExact::mul` focused source cut (2026-10-22)

This packet records a narrow Charon/Aeneas extraction from the pinned actual `aspis-core` field sources. A top-level harness calls `WideExact::mul`; `field.rs` and `field/wide_exact.rs` are byte-identical to the pinned source snapshots. This is source/emission evidence only, not a Lean refinement theorem or proof that the generated operation agrees with a separately modeled arithmetic operation.

The extraction selected `crate::focused_wide_exact_mul` and `crate::field::wide_exact::_::mul`. `WideExact::mul` and its reachable QM31, CM31, M31, `mul_u`, and `mul_by_r` operations are transparent. `WideExact::add`, `WideExact::square`, and `WideExact::mul_qm31` remain opaque; they are outside this multiplication cone. The generated function body is present in `evidence/aeneas/generated/AspisR1S9ActualWideMulCutV1/Funs.lean`.

Charon completed with exit 0 in 2.202 s; cgroup peak was 112,717,824 bytes, process maximum RSS 207,040 KiB, swap 0. It emitted 18 functions and 4 types in LLBC (`c977a36e…` SHA-256). The raw LLBC JSON is intentionally omitted; `evidence/charon/declaration-inventory.json` retains the exact LLBC hash, error status, function/type counts, source spans, body hashes, and required declaration opacity inventory, checked by `check_declaration_inventory.py`. Aeneas completed with exit 0 in 0.301 s; cgroup peak was 70,455,296 bytes, process maximum RSS 70,752 KiB, swap 0. It emitted nonempty Lean Types/Funs and translation JSON (`28f7fe1c…` SHA-256). Both phases ran after fresh common admission under actual verified cgroups with MemoryHigh=2 GiB, MemoryMax=4 GiB, MemorySwapMax=0. Raw admission and reservation records are included.

The parent attempt20 sourcecut check initially rejected a stale duplicate `input/src/Cargo.toml` identity entry; no extraction was run for that attempt. Attempt21 removes only that erroneous duplicate identity entry and passes the sourcecut checker before extraction.

No ELF, shared object, object file, or Lean compiled object is included.
