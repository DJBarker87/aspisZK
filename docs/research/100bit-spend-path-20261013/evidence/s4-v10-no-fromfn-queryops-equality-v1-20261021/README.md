# S4 V10 no-from_fn query operation equality

This focused Lean result defines `noFromFnQueryOps` by taking `concreteCandidateQueryOps rest` and overriding only `dots` with the callback using the V10 execution record whose unused `arrayFromFn` and `wideLimbCount` slots diverge. It proves the resulting `QueryOps` equals the concrete candidate record. Congruence then proves equality of `queryWithOps` and `query_loop` for every input and every `Result` outcome; there are no success, canonicality, scanner, or acceptance premises in these equality theorems.

The callback equality is the already checked `no_from_fn_dots_eq_concrete` kernel theorem. This is a selected Lean execution-model equality, not adoption or a Rust source/runtime refinement claim. It removes dependence on the old P6 record slots from this candidate query execution model. Existing source, compiler/extraction, and upstream caller boundaries remain as stated in the kernel packet.

## Verification

- Module: `AspisR1S4V10NoFromFnQueryOpsEqualityV1`
- Target: `S4NoFromFnQueryOpsEqualityV1.lean`
- Lean 4.32 binary SHA256: `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`
- Launch revision recorded in receipt: `3af931da4e590aea7748f6e45a26550a1b099f08`
- Exit: 0; wall: 9.551 s; peak aggregate RSS: 3,934,437,376 bytes; peak process RSS: 4,008,951,808 bytes; process swaps: 0
- Object SHA256 (receipt only; binary omitted): `dcf017e2fdeb86bf7db7d6373ff7b187bc8891dbb23618b3896d38549ef15186`
- `#print axioms` for all three exported theorems: `[propext, Classical.choice, Quot.sound]`.

The exact loop `.olean` owner used by this compile is pinned in `direct-imports.json`. Its producer receipt records source SHA `6eec6a3f…`, while the currently tracked source snapshot is different (`c398ba41…`). This provenance mismatch is explicit; no identity claim is made between those source snapshots. The selected module object hash itself is exact.

No binaries are included.
