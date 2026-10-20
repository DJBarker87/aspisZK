# Terminal v4 generated external-model integration candidate

This separate candidate packet keeps production sources and the generated Aeneas output unchanged. Its external-module overlays progressively replace selected generated external declarations with Lean implementations and focused axiom reports. The first overlay imports `TerminalStandardOperationModelsV1` for `Array.map`, `Result.map`, and `Result.map_err`; the module elaborates successfully. The second adds a namespace-rebound `Range.clone` body copied from the accepted `SumHighStdModels` implementation and proves `range_clone_usize` without axioms. The third adds an `Option PartialEq::eq` definition by explicit nested pattern matching and reports that it has no axioms.

The generated source inventory contains 17 Funs axioms and one Types axiom. The latest overlay removes five Funs declarations, leaving 12 Funs axioms plus the IntoIter type. The Option implementation is a candidate model; equivalence to the Rust standard-library body remains open. Iterator folds, IntoIter operations, u16 primitives, and other remaining externals are also open.

A full generated `Funs.lean` elaboration with terminal `#print axioms` was attempted under the existing 4 GiB aggregate cap and stopped after 26.26 s when aggregate Lean RSS reached 4,342,841,344 bytes. The log is empty, no object was produced, and no higher-cap retry was made. The next attempt should isolate the terminal dependency closure.

These checks establish overlay elaboration and the reported local model theorems only. They do not establish Rust standard-library source correspondence, every terminal callback, or Rust-to-Lean semantic refinement.
