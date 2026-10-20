# S3 low-array to grouped source-row composition

This focused Lean 4.32 target composes the checked low-array totality/canonicality result with the checked V3 grouped-inactive source-row theorem. It explicitly maps each low-array record with `toActualS`, proves canonicality in the grouped helper's nominal carrier, and returns the source-row conclusion for every successful grouped call.

The result concerns the two helper cuts and the explicit nominal array adapter. It does not establish the enclosing Rust `Weights::pair` control-flow, the `core::array::from_fn` Rust standard-library correspondence, or the final production caller continuation.

The accepted source is `S3PairLowGroupedRowCompositionV1.lean`; its SHA-256 is `c037a89c099eb1f83a872fd6df6de840b888127f2b32f776c67ab36780cbfc70`. The focused compile used `-j1 -M 4400` with no option overrides. Axiom output is recorded in `evidence/attempt-v12/lean.log`.

The preceding v10/v11 attempts are diagnostics only and are not release results. v10 failed on private source-row names and an oversized restatement; v11 exposed an invalid theorem-as-proposition alias and use of a proof-local canonicality witness in the result type. The v12 source changes those APIs and is the sole accepted compile here.
