# S3/S9 current source-repin candidate

This candidate closes the mathematical S3 grouped-pair identity and S9 factorization against the current source-shaped model. The S3 model's 64 active-mask literals are now checked equal, element for element, to the extracted `crates/aspis-core/src/r0/opening.rs::COPY_ACTIVE_ROW_MASKS` declaration. The extracted `opening::inactive` helper is also proved to return the S3 model's grouped inactive predicate whenever its Usize input carries the corresponding S2 source row.

Checked additions in this packet:

- `S3InactiveExecutionBridge.inactive_mask_exec_spec`: successful in-range helper result equals the low-bit predicate of the exact indexed extracted mask.
- `S3InactiveModelBridge.extracted_masks_eq_model`: all 64 extracted masks equal the model's `activeRowMasks` list.
- `S3InactiveModelBridge.extracted_mask_value_eq_model`: each successful extracted array read agrees with the same model list entry.
- `S3InactiveModelBridge.actual_inactive_eq_source_model`: the extracted helper result equals `sourceInactive` for the same row.
- `S3InactiveModelBridge.actual_inactive_eq_grouped_model`: under an explicit row-value equation, the extracted helper equals `inactiveAtGroup`, and the existing `s3_grouped_pair_exact` theorem supplies the algebraic regrouping.

The remaining source boundary is the caller's `Variant::S2.row(16*j+bit)` value equation (and surrounding `Weights::raw`/`Weights::pair` execution). The current `actual_inactive_eq_grouped_model` keeps this row equation as an explicit premise; this packet does not claim an extracted/refined `Variant::row` call or a `Weights::pair` theorem.

Rust source pins and exact focused Charon/Aeneas/Lean receipts are under `evidence/s3-s9-current-repin-20261020/classification-source-cut/`. Lean objects remain in `/tmp/s3-s9-inactive-source-cut-v1-20261020/lean-objects` and `/tmp/s3-s9-current-repin-20261020-objects`; this packet contains no object files or executables.
