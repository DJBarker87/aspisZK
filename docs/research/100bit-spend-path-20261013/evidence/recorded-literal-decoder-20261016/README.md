# Actual recorded-run decoder completion

`RawCutLaterTableLiteralWords` proves recovery of each committed word component from the current first-read table. `LiteralTableChoiceWords.constructed_components` identifies those components with the actual recorded-view constructor. `RawLiteralRecordedDecoder.actual_run_decodes_and_follows` therefore supplies all-33-round completion of the concrete table-only decoder for the enriched actual run, without an assumed word-agreement hypothesis. Actual message validity, strict row0/2/30 parser facts, the query bound, and the single fixed-IV collision exclusion remain explicit.

`RawPublicInitRecovery` reconstructs public bytes from the initial hash input. `RawAdaptiveLiteralDecoder` preserves density when a public statement is selected from the current address/table, without a union over statements. Correct public selection for all later rounds remains a separate deterministic obligation; the recorded-run decoder theorem still receives the run's public statement.

The compiled-run corollary, source terminal acceptance, efficient extraction and final numerical 100-bit bound remain open.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawCutLaterTableLiteralWords` | 2.364 | 3631380 | 4 |
| `LiteralTableChoiceWords` | 1.823 | 3634576 | 2 |
| `RawLiteralRecordedDecoder` | 1.683 | 3646592 | 1 |
| `RawPublicInitRecovery` | 1.75 | 3547008 | 3 |
| `RawAdaptiveLiteralDecoder` | 1.532 | 3630972 | 2 |
