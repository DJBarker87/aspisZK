# Terminal v4 generated callback / standard-operation bridge

This focused Lean check builds the exact generated v4 `TypesExternal`/`Types` slice, then checks the two actual generated `terminal_qm31` callback bodies against the existing executable models for Rust `Result.map` and `Result.map_err`.

`TerminalV4GeneratedTerminalCallbacks.lean` preserves the callback declarations copied from generated `Funs.lean` lines 946–1001. The checked composition proves both branches: on a successful terminal result, `map` extracts the first QM31 component and `map_err` preserves success; on the error branch, `map` preserves the error and the source callback maps it to `Error.Public`. This checks the generated callback/model interaction without compiling the complete 305 KB generated `Funs.lean` or claiming a full model of every external.

The compiled source files and per-target receipts are under `sources/` and the named attempt directories. Lean 4.32 used the shared serialized focused runner with `-M3200`, one job, and zero process swaps. The operation-model dependency is the already accepted `TerminalStandardOperationModelsV1` object; its source is recorded in the prior evidence packet `evidence/terminal-standard-operation-models-20261019/`.

The v4 translation still exposes 15 Funs external templates and one Types external template. The Funs list is included in the separate Aeneas packet `evidence/terminal-qm31-fromfn-copy-candidate-v4-aeneas-20261019/nuc-run/receipts/funs-external-axioms.txt`. Existing models are available for `Result.map`, `Result.map_err`, and `Array.map`; this packet only verifies the two terminal callback/result operations. Array-map callback semantics and all remaining fold/iterator/numeric/Option externals remain separate obligations. The single `TypesExternal` axiom for `core.array.iter.IntoIter` remains an admitted type boundary.

Attempt `terminal-v4-generated-terminal-callbacks-20261019` is the preserved first diagnostic (one tuple destructuring goal remained). Attempt `terminal-v4-generated-terminal-callbacks-v2-20261019` is the changed successful check. No shared/canonical generated sources were modified.
