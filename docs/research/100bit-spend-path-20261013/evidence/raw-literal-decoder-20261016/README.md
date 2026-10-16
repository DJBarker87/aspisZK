# Actual raw-byte decoder completion and literal density reuse

`RawUnifiedDecoder` constructs the raw-byte background decoder from the existing canonical bounded decoder and transfers its follow behavior and fixed-round bound exactly. `RawLiteralDecoderCompletion.decodes_erased_and_follows` proves successful raw decoding of the actual erased transcript, current message and challenge for every one of the 33 rounds. Its premises are the message schedule, trace consistency, query budget and the single raw collision exclusion; decoder completion is no longer assumed.

`LiteralDecoderEnrichment` restores supplied literal commitment words while preserving the erased sampler, and reuses the checked literal classifier density. Words may be selected from the decoded prefix and current message before the current challenge. The concrete table-derived word selection, successful-run enrichment, terminal source correspondence and final numerical bound remain separate work.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawUnifiedDecoder` | 1.695 | 3560308 | 2 |
| `RawLiteralDecoderCompletion` | 1.772 | 3641600 | 2 |
| `LiteralDecoderEnrichment` | 1.781 | 3645148 | 3 |
