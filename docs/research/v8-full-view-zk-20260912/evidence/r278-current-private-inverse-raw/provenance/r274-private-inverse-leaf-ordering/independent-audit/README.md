# R274 independent metadata ordering audit

`audit_independently.py` independently decodes the raw R266 LLBC, follows typed declaration references from Fun0/Fun1 using the pinned Charon visitor structure, validates the emitted dependency-first order, and compares the ordered output with its input after removing only `translated.ordered_decls`. It performs no translation or build.

The audit passes: the input, output, and pinned `reorder_decls.rs` hashes match the recorded values; 34 reachable declarations (Type 6, Fun 15, Global 3, TraitDecl 5, TraitImpl 5) are ordered exactly once; all 54 dependency edges and 309 typed reference occurrences match the generator audit; there are no cycles, unknown reference shapes, or non-vtable missing references.

The only missing references are the three specifically named vtable metadata references in TraitDecl 0, 19, and 20 to Type 5, 43, and 44. The current generator now checks source kind, vtable path, Type target, label suffix, and full pinned source hash. The preserved `rejected-metadata-before-label-guard` directory records the earlier predicate version. No trait default references were reachable; pinned Charon treats any such default reference as reachability-only (`insert_node`), not as a dependency edge.

This is a structural metadata audit only. It says nothing about successful translation, source correspondence, or theorem semantics.
