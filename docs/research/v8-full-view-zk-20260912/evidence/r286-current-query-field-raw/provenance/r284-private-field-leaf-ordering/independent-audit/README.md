# R284 independent metadata audit

`audit_independently.py` independently re-reads the frozen R281 LLBC, R284 ordered LLBC, root-body inspection, and pinned Charon `reorder_decls.rs`. It checks each artifact against its recorded SHA-256, reconstructs the reachable typed declaration graph from R281, verifies all twelve output declaration rows are unchanged, checks dependency-before-use order, and confirms the only serialized JSON difference is `translated.ordered_decls`.

The full input declaration tables contain 3 types, 8 functions, 1 global, 0 trait declarations, and 0 trait implementations. The two roots are external (`item_meta.is_local=false`) structured LLBC entries at file id 0, lines 874 and 927. The attached root inspection records the frozen `field.rs` source hash `639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499`; the root rows and inspection agree on IDs and spans. Because the input contains no trait declarations or implementations, trait defaults are absent from this graph.

This is a mechanical metadata audit. It does not accept the external roots, establish source semantics or correspondence, translate LLBC, or close a theorem or release gate. The root acceptance decision remains with the lead.
