# S5 finish field-product proof packet v2

This packet contains a focused Lean proof that successful `finish_query_dot` output decodes to the finite field product sum over its ordered query rows. It replays the Delta decoder from its exact source, then recompiles this theorem against that exact Delta object.

The dependency chain is: `FinishDotReturnedDecodedValueV1` (source/object/receipt retained from the accepted local run) → `FinishDotReturnedDeltaDecodeV1` (exact source SHA and fresh NUC receipt in `nuc/delta-evidence`) → `FinishDotReturnedFieldProductV1` (fresh NUC receipt in `nuc/attempt/field-product-evidence`). All theorem audits list only `propext`, `Classical.choice`, and `Quot.sound`. No compiled objects are included.

The older `08a36…` Delta object and the failed v4 attempt are historical only; the selected proof here is the fresh object `62d96b…`. The NUC source revision field is descriptive, not a Git commit; each source is identified by its SHA-256. Scope and source/runtime adoption limits remain as described in the Lean source and manifest.
