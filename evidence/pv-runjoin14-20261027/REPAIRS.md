# Authorized records extraction repairs (D274)

Entry revision: 9128568ac068bee9527806edc32982a35010c706.

1. In `records`, pair_forest_copy_builder.rs:229, verbatim:

```diff
-    let pair = &input.pair;
+    let pair = input.pair;
```

This copies the identical immutable value instead of retaining a shared borrow.
`PoolV1PairInputNoteWitnessV1` derives `Clone, Copy` at
`crates/aspis-statement/src/pool_v1/pair_trace.rs:71` (type declaration at 72).
No signature/type or other function change. Existing `raw(&pair.field)` calls
continue to borrow the same field values from this copy. No extra repair yet.
