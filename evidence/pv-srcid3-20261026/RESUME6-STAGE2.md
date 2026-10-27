# Pure reference call equation

PV_Src_DynamicCallEquation.reference_call proves the extracted owned reference
returns its complete field-level record pair for arbitrary input, output,
recipient option, change, snapshot, asset, and supplied root array.
PV_Src_DynamicCallEquation.call preserves the complete Result of the actual
pair_empty_roots helper. It introduces no success or external-effect premise.
PV_Src_PureCallEquation.call specializes that equation to the already explicit
pure ExternalReference.dictionary (no typeclass hypothesis remains).

Attempts 37103 and 37104 passed with standard axioms. These are exact pure
reference dictionary equations, not an identification of the opaque shipped
BuilderForestAdmissionPort.Records leaf. The still required P6 full-mapper
association is not silently treated as a Lean equation. Therefore the deployed
compile_call field remains OPEN and PV_Src_Premises remains 5 → 5.

Next independent work: the actual root-helper recurrence and exhaustive
unstubbed full-mapper P6 partitions (recipient present/absent × selected first/
second). Four partitions cover the entire input space without word bounds.
Each compares all 20 fields, including both root arrays computed by the real
helpers. The heavy step is expected in bounded CBMC after optimized compilation,
not arithmetic in a debug binary. One capped scope at a time is maintained.
