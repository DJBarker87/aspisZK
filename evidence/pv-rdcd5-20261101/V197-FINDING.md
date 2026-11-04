# V197 — FINDING: complete Result carriers disagree

`R1Z.PV_RDCD5_ParserErrors.carrier_mismatch` is kernel checked at78213.
For the original empty `Slice U8`, the EXISTING
`ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes` returns
`fail .panic`, while `PV_RDCD4_BytesSource.qm []` returns
`fail .arrayOutOfBounds`. The literal complete-Result transport is false.
No input guard, short-circuit order or failure constructor is silently changed.

ParserWindows passed78205, V197 passed78208, ParserFlat passed78209. These
prove their local owned-model statements; none establishes the original op71
association. Attempts78206/78207 were genuine elaboration failures, repaired
before the78208 retry; their emitted sorryAx diagnostics earn no credit.

Counterexample receipt: exit0, wall0:01.12, peak2592852KiB, swap0,
source revision in lean-78213/receipt.json; printed axioms are exactly
propext/Classical.choice/Quot.sound. No native source or dictionary was edited.
No Kani, extraction, fmt semantics, error erasure or success-only transport.
Before/after endpoint premises removed/added/changed: zero. T remains the same
three fields; V370/D381/D386 and physical-observer obligations remain.

Stop the false literal identification under r1p rule4; continue V233 and V236.
A future corrected faithful parser model would need explicit error-constructor
transport at the original arbitrary-slice domain and its own complete proof.
