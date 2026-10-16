# Deterministic reuse of the legacy decoder carrier

`RawBoundedTrace` projects an unrestricted raw-byte oracle trace to the legacy padded-address carrier through canonical addresses. Oversized inputs are omitted, never sent to a fallback address. Padding aliases remain undefined. This preserves every retained query, its exact first-read table and suffix, and never increases the distinct-read count. The generic partial-embedding lemmas also preserve first-read order and transport compatible bad events.

This is deterministic trace bookkeeping for reuse of the existing decoder proofs. It does not bound adversarial input length, transfer a probability law across a noninjective map, or close the decoder-completion theorem. `TraceBadWitness` supplies the converse of the existing first-read bad-event inclusion for the next collision-exclusion bridge.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `PartialAddressTrace` | 1.074 | 1822216 | 6 |
| `CanonicalRawTrace` | 0.862 | 1812924 | 6 |
| `PartialAddressOrder` | 1.882 | 1812224 | 3 |
| `PartialAddressImage` | 0.963 | 1815980 | 5 |
| `RawBoundedTrace` | 0.981 | 1812824 | 8 |
| `TraceBadWitness` | 0.899 | 1808244 | 2 |
