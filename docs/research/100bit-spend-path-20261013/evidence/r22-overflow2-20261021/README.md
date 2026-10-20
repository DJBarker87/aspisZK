# R22 overflow continuation receipts

Stage 1 adds isolated frozen-source contracts for M31/CM31/QM31 decoding,
Reader.raw and Reader.k. No shipped source changes. The generator binds each
copied declaration to frozen revision b2727acd3abf79315d18b754a260f58f4b1c6326;
source-shaped field types are tool context, not a complete extraction proof.

Attempts 01–08: 01 is a compile diagnostic; 02–08 pass. Decoder harnesses
exercise their fixed wire widths (4/8/16). Reader.raw harnesses exercise all
byte values, cursor positions and lengths within a 64-byte backing allocation.
Reader.k is checked over a fixed 64-byte allocation using verified summaries.
**These reader bounds do not cover whole checkpoints.** Contract declarations
have wider domains than those early harnesses: do not cite those early results
as universal verified contracts or use them to discharge R22. Stage 2 narrows
and expands the coverage explicitly. Fixed-width decoder calls in the source
have the tested widths; later contracts restrict those widths explicitly.

Full attempt fields are in attempts/*/receipt.json; summary.tsv is compact.
Exact commands, limits, frozen source revision/hash, dependency fingerprint,
wall, RSS, swaps, errors and the N/A Kani axiom report are preserved. No Lean
theorem or endpoint change is made in this stage, so no premise deletion is
claimed. Sources/ retains small historical tool inputs for coverage audit.
