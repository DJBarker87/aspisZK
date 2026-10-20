# Original emitted polynomial: operational Aeneas fold adapter

This packet covers the frozen source `verifier::polynomial` at revision
`c8ea8dd49c81ab970b9dbee8d8b47718f9beb005`. The authoritative source is the
retained `verifier.rs` pin with full-file SHA
`8a704eea668d04ca173290ca894c7cb0ab1f29abef4fec9bb49fbb36476779ea`; the
exact function is bytes `[12595,12695)` with SHA
`ca19094cb9ea4f1b293554b0ec68d055ccc1dd71488f16f6e5f5043c631e48a7`. The
Aeneas extraction input is a separate assembled file whose corresponding
function is bytes `[33146,33246)`. The checker proves those 100 bytes are
identical; it does not mislabel the extraction-input offset as the verifier
source offset.

The pinned original generated `verifier.polynomial` declaration and closure
callback are checked in full by `check-original-polynomial-fold-source.py`.
It checks the generated function signature/body, callback captures and
arguments, all operation order, closure-state passthrough, and the complete
adapter expression. Its structured result is `source-check.json`.

`AeneasOriginalPolynomialBodyAdapterV1.lean` ports the whole generated body by
replacing its `Rev.fold` call with the selected Aeneas `Rev.next` loop and
mapping generated nominal Wide arithmetic/field lookup to the checked
current-Wide callback. It proves equality to the current unrolled polynomial
as a `Result` for every byte slice and input value, including success and
failure outcomes. The immediate imported Lean owner is pinned at object
`ad604c3b46631964678ff6d5ca3147781317d2a191d3bc32c078351861ff953a`; its
source is included in `dependencies/` and its dependency evidence is the
separate `aeneas-current-wide-polynomial-fold-consumer-v8-evidence` packet.

No generated `Funs`, `FunsExternal`, or `TypesExternal` owner is imported by
the Lean proof; generated declarations are retained only as source pins. The
actual Aeneas iterator source pins and actual `Rev.next`/`Range.next_back`
refinement are included. The one remaining correspondence is Rust core's
`Range<usize>::rev().fold` to the selected emitted Aeneas operational loop.
This packet does not claim that standard-library correspondence or adoption
of an alternate Rust body.

Focused NUC Lean check: Lean 4.32.0, `-j1 -M 4400`,
`MemoryHigh=1GiB`, `MemoryMax=2GiB`, `MemorySwapMax=0`; exit 0, wall 2.106s,
peak process RSS 3,688,952 KiB, cgroup memory peak 374,325,248 bytes, scope
swap 0, and no memory events. Both `#print axioms` reports are
`[propext, Classical.choice, Quot.sound]`. Exact command, source/import pins,
preflight, Lean output and `/usr/bin/time -v` log are in `attempt/`.
