# Actual compiled decoder output and public-free opening recovery

`RawCompiledTranscript` identifies the compiled prover's actual public/proof output, transcript, chain, challenge and first-read frame. `RawCompiledDecoderCompletion.actual_compiled_transcript` uses those identities to make the concrete decoder's returned tuple exactly the actual compiled protocol transcript/message/challenge for all 33 rows. It still receives the actual public statement and retains source-format/collision/query premises.

The opening public-recovery walker strictly crosses the reseed frame and then uses the public-free initial walker. Its cells theorem and actual chronological trace theorem derive the recovered public statement from concrete lookup/order facts under the existing collision exclusions. The initial walk is explicitly specialized to 27 semantic steps. The selector takes an address/table and fixed tag, not the actual public statement.

Actual phase dispatch, full adaptive compiled completion, source terminal acceptance and efficient extraction remain open. No complete 100-bit soundness claim is made.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawCompiledTranscript` | 1.585 | 3628940 | 4 |
| `RawCompiledDecoderCompletion` | 1.532 | 3645456 | 1 |
| `RawPublicOpeningWalk` | 1.75 | 3552720 | 4 |
| `RawPublicOpeningWalkCells` | 1.583 | 3550260 | 1 |
| `RawPublicOpeningPrefixTrace` | 1.577 | 3546492 | 1 |
