# J1 append binding map reuse

This note records the mechanical transport used by `R1AppendBindingMap` and
`R1SpendRelationMap`. It concerns the current Lean predicates only; it does
not establish a Rust refinement or a source-level append-state invariant.

`SpendDataMap.mapPublic` preserves `nextPairIndex` literally and maps each
digest-valued field coordinatewise. `AppendPath.step` therefore keeps the
same `digestBitZero` branch. The node-compression equality is reused from
`R1PoseidonMap` as `PoseidonMap.map_nodeCompress`; a small local wrapper makes
the definitional equality with `SpendDataMap.digest` explicit. Frozen empty
nodes are transported coordinatewise by `map_natCast`, without unfolding the
finite empty-root table. `map_pathPrefix` then follows by induction on the
requested prefix length, applying the one-step map theorem at each recursive
step; it does not expand the twenty-level path.

For `AppendBinding`, the output-pair equation transports through
`map_outputPair`. In the reverse direction, injectivity of the field
homomorphism lifts both the `nextRoot` and active carry-frontier equalities
back to the source field. In the forward direction, applying the homomorphism
to those equalities gives the target-field claims. The only assumptions are
`[Field K]`, `[Field L]`, and the ring homomorphism `f : K →+* L`; its
injectivity follows from the field instances. No append index is excluded.

`R1SpendRelationMap.rspend_map_iff` uses this equivalence for the sixth
conjunct of `Rspend`, alongside its previously established coordinate-map
lemmas. The new map file also prints axioms for the frozen-root, step,
prefix, output-pair, and full append-binding results.
