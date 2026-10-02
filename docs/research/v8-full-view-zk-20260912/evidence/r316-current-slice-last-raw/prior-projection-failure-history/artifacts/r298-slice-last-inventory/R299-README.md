# R299 Slice.last LLBC projection

This is a mechanical, metadata-only projection of the frozen R294 LLBC input. It retains only the existing `Type[9]` (`core::option::Option`) and `Fun[12]` (`core::slice::<impl>::last`) rows, in the authorized `ordered_decls` order: Type NonRec 9, then Fun NonRec 12. All declaration arrays preserve their original lengths and indices; other rows become null. `item_names` and `short_names` are filtered to those typed IDs.

`project_slice_last.py` is the reproducible generator and audit. It asserts the frozen input, inventory, pinned reorder-rule, and serializer-reference hashes before processing. Hash-cons IDs and values are retained verbatim where reachable; the serializer pattern is referenced from the schema-audited R220 projection source, while R299 performs its own full decoded-data checks. The audit verifies all output deduplication references resolve, output hash-cons IDs are a subset of the input IDs, retained rows decode identically with no cycle markers, and no decoded metadata changes outside the authorized row/name/order projection. The two-row typed closure is checked against the R298 inventory: one Fun-to-Type edge, no missing references, cycles, or unknown reference shapes.

Input SHA256: `bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f`.
Output SHA256: `8dc807df3ff65a0bb01c27eca2a4c98de5d1f499ac566db44875dffba4050aca`.

The projection retains 19 of 422 hash-cons definitions and drops 403 unreferenced definitions. The declaration array lengths remain Type 63, Fun 243, Global 33, TraitDecl 32, TraitImpl 47. No translation, build, Lean execution, or source-semantics claim is included; the lead must review the projected artifact before any later translation step.
