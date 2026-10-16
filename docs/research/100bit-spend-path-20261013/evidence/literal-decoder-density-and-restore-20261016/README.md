# Literal decoder density and restoration

`RawLiteralDecoderDensity.density` proves ChainDensity3 for the concrete raw-byte background decoder using the existing all-33-round classifier bounds. Its word selector may depend on the current table and decoded prefix/message, but not on the current challenge.

`LiteralTableWordChoice` defines a table-only selector; `LiteralTableChoiceRun` proves it obtains roots from the actual parsed messages. `LiteralWordAgreement` requires equality only for commitment components already present by the current round. `RawLiteralDecoderRestore` uses that condition to turn actual erased decoder completion into enriched decoder completion. `RawCutLiteralAllFrames` proves all adjacent first-read frame orderings, including the initial, reseeded and query special cases.

The component equality for the concrete selector is the next bridge, not a premise claimed discharged here. Source terminal acceptance, efficient extraction and the final numerical 100-bit bound remain open.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawLiteralDecoderDensity` | 1.941 | 3633220 | 1 |
| `LiteralTableWordChoice` | 1.985 | 3625328 | 3 |
| `LiteralTableChoiceRun` | 1.808 | 3629168 | 4 |
| `LiteralWordAgreement` | 1.889 | 3640236 | 2 |
| `RawLiteralDecoderRestore` | 1.683 | 3639572 | 1 |
| `RawCutLiteralAllFrames` | 1.883 | 3643556 | 1 |
