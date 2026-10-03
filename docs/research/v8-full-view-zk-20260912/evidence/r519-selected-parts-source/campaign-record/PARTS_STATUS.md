# R508 selected `shared_gamma::parts` projection

- Captured LLBC: `.r21-scratch/r508-selected-prepare-source/R508SelectedPrepare.llbc`
- Captured LLBC SHA-256: `600705e63cb7ba718e09a11e2da257c2fccf097173bfea00f294446265d32bc8`
- Root: `Fun107`, exact item `aspis_v8_performance_host::r17_host_relation::shared_gamma::parts`
- Source: embedded `../shared_gamma.rs`, bytes match pinned source SHA-256 `75c26014c9900221445c14536d966f3d9267b53b331709099afda6374bf72552`
- Declaration span: lines 5–10; source text is retained in `reachable-nodes.json` and original LLBC.
- Body status: `Structured`.
- Signature source form: `fn parts(v: K) -> Channels`, with `type Channels = [[M31; 3]; 3]`.
- Actual selected call site: `Fun18` (`shared_gamma::five`), stmt `23682`, source `shared_gamma.rs:43:26–55`; it is in three nested `Loop` contexts in LLBC. Exact typed arguments, destination, and source location are in `typed-chronology.json`.
- Direct structured-body calls found: Fun94 (`aspis_core::field` inherent `add`) and Fun175 (`aspis_core::field` inherent `add`). Full declaration/type/global dependency edges are preserved in `dependency-edges.json`.

The original pinned typed-dependency visitor from the R490 selector was reused with only the LLBC input SHA/path and root changed. The fail-closed traversal found 10 reachable nodes (5 Fun, 3 Type, 2 Global), 191 typed edge occurrences, no missing referenced rows, no unclassified ID-plus-generics records, and no reachable declaration outside `ordered_decls`. `R519SharedGammaPartsSelection.llbc` is a projection changing only `translated.ordered_decls`; its other JSON values and byte prefix/suffix match the source exactly. Projection SHA-256: `e614a35673713638504c4c4e83387dbee819805a510094aff7bc76b45826e606`.

This is extraction/projection evidence only. No Aeneas translation or Lean compilation was run, and no source-to-model semantics claim is made. Aeneas preprocessing has previously depended on a broader function map than a narrowed ordered-declaration projection supplies; therefore the lead should inspect the pinned prepass behavior before selecting this projection for translation. Do not infer that the projection itself resolves the prepass dependency.
