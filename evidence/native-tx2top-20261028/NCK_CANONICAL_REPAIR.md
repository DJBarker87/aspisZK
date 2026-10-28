# Final co-import ownership repair

L036 failed before theorem elaboration:import NCK_Stage2Cuts would duplicate
`AdapterRw.r1_pool_adapter.owned.stage2_owned.eq_1`, already exported by
canonical S2W_OuterErasure in the D189 closure. Independent compilation had
materialized a deferred equation theorem in a different consumer environment.
This was not a false theorem, changed Rust body, or missing cryptographic law.

Only NCK imports are adjusted. The owned-body proofs now preload canonical
S2W_D189Wrappers; NCK_Stage2Shape consumes NCK_Stage2Cuts, and NCK_Admission
consumes that shape module. The validator length proof preloads the same
canonical SDK closure; the snapshot-read proof consumes NCK_Snapshots.
NCK_CommonCuts preloads NCK_ResumeDomain/VTop_Cuts, the canonical owner of
stage equations; NCK_TailCuts consumes that chain. Statements and proofs are
unchanged. NCK_SecondBinding is rebuilt for its changed dependency selection.

No existing proved module, selected SInt2 object, shared workspace, launcher,
reservation or source owner is edited. All replacements are NCK objects in
this lane's private cache. This is a source/dependency change justifying the
focused rebuilds and one new co-import audit, not an unchanged regression.
