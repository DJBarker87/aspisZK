# Canonical background-decoder support and transport

The existing 33-row unified decoder now has a proved all-continuations canonical-address property for its own queries and pending background reads. Generic partial-address embedding preserves background follow exactly while skipping unrelated raw queries. Address restriction and renaming preserve the independent-answer law exactly.

These facts allow the existing bounded decoder to be used over unrestricted raw bytes through canonical addresses. They do not assert injectivity of the padded carrier's `toBytes` map, restrict adversarial input length, or supply the remaining literal-word enrichment/source correspondence.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `BackgroundAddressMap` | 1.084 | 1811408 | 6 |
| `BackgroundAddressFollow` | 1.009 | 1821840 | 2 |
| `BackgroundAddressRestriction` | 0.887 | 1809704 | 2 |
| `BackgroundCanonicalLabels` | 1.629 | 3551440 | 4 |
| `UnifiedDecoderCanonical` | 1.585 | 3556276 | 2 |
| `RawBackgroundCompletion` | 0.904 | 1809764 | 2 |
