# R12 binary commitment word packet

Design and precise premise accounting: `../../design/R12-WORDS-20261020.md`.
Five new modules, 20 new theorem audits; all final targets exit 0, standard
axioms only, zero swaps. Three unchanged dependency modules were rebuilt
privately; eight additional audits. `manifest.json` contains exact final
receipts, commands, revision/source hashes and import fingerprints.

New targets: BinSourceCommitmentWords, BinSourceCommitmentFrames,
BinSourceCommitmentLiteral, BinSourceCommitmentOpening, BinStage2FoldedWord.
The C1 initializer and folded row-30 frame determine the canonical binary
cut words; logged accepted strict openings project to those words; the actual
row-0/30 literal constructors preserve source challenge/block and state.
Stage-2 folded-leaf slicing and its conditional projection use the retained
emitted control body and named backend/conversion boundaries.

Remaining: R10 chronological global-log composition/consistency and read
budget; R13 source multiproof acceptance, read containment and strict field
decoder transport; folded payload/checkpoint root join; concrete leaf backend
and salt conversion; prepare/caller re-pins and scalar transport; R15
checkpoint provenance; full word-bearing transcript/Checks composition.
No deployed-to-model closure or fresh release replay is claimed.

Run `python3 .../evidence/r12-words-20261020/audit.py` to check the final packet.
Historical attempts are retained separately, including failed logs with
elaborator-generated sorryAx. No failed attempt is accepted evidence.
No verifier/source modification, shared-object overwrite, key operation or push.
