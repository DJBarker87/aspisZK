# Original emitted polynomial: operational Aeneas fold adapter

This packet addresses the frozen original source `verifier::polynomial` at
`c8ea8dd49c81ab970b9dbee8d8b47718f9beb005` (source pin in `pins/`). The exact
100-byte Rust function is pinned at bytes `[33146,33246)` of the emitted input
snapshot; its SHA-256 is `ca19094cb9ea4f1b293554b0ec68d055ccc1dd71488f16f6e5f5043c631e48a7`.
The original generated `verifier.polynomial` body and its generated closure
callback are also retained as source pins. `check-original-polynomial-fold-source.py`
checks the whole generated function body, callback dataflow/return, Rust source
span, and the complete adapter expression; it passed and its structured output
is `source-check.json`.

`AeneasOriginalPolynomialBodyAdapterV1.lean` ports the whole generated body by
replacing only its `Rev.fold` call with the selected Aeneas `Rev.next` loop and
replacing generated nominal Wide operations/field lookup with the previously
checked current-Wide arithmetic/parser callback. Its theorem proves equality to
the current unrolled polynomial as a `Result` for every byte slice and input
value, so both success and failure outcomes are covered. The theorem uses the
already-green `AeneasCurrentWidePolynomialFoldConsumerV1` object
`ad604c3b46631964678ff6d5ca3147781317d2a191d3bc32c078351861ff953a` and its
pinned source is included under `dependencies/`.

No generated `Funs`, `FunsExternal`, or `TypesExternal` owner is imported by
the Lean proof; the generated files are retained only as source pins. The actual
Aeneas iterator source pins and actual `Rev.next`/`Range.next_back` refinement
are included. The remaining correspondence is precisely Rust core's
`Range<usize>::rev().fold` to the selected emitted Aeneas operational loop.
This packet does not claim that library correspondence or adoption of the
candidate body. The earlier explicit-unroll Rust candidate is not used here.

Focused NUC Lean check: Lean 4.32.0, `-j1 -M 4400`,
`MemoryHigh=1GiB`, `MemoryMax=2GiB`, `MemorySwapMax=0`; exit 0, wall 2.106s,
peak process RSS 3,688,952 KiB, cgroup memory peak 374,325,248 bytes, scope
swap 0, no memory events. Both `#print axioms` reports are
`[propext, Classical.choice, Quot.sound]`. Exact command, source/import pins,
preflight, Lean output and `/usr/bin/time -v` log are in `attempt/`.
