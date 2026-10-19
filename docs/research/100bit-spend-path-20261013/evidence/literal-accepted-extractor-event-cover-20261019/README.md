# Deterministic accepted-extractor event cover

`LiteralAcceptedExtractorEventCover.accepted_extraction_failure_covered`
proves that, under the explicit semantic parse/check, matching/opening,
accepted-support, and typed-word premises, an actual extractor result of
`none` implies either a classifier `hitFrom` event or failure of the actual
five-lane GS byte decoder bank. The proof invokes the checked no-hit
completeness theorem and does not assume a probabilistic event-cover premise.

This is a deterministic caller lemma. It is not the unrestricted shared-ROM
bound and does not by itself prove that deployed acceptance establishes the
listed semantic premises. The existing adaptive fresh-challenge plus
actual-bank mass theorem can consume the event inclusion once the protocol
caller discharges those premises.

The focused Lean 4.32 receipt, source snapshot, OLean, exact runner, and
transitive import-closure report are in `attempt-v15/`. It passed with exit 0,
14.13 seconds wall time, 3,158,851,584-byte maximum RSS, zero process
swaps, and standard axioms `[propext, Classical.choice, Quot.sound]`.
The R0P namespace precedence/coalescing manifest records the selected hashes.

These focused compiles are working evidence. Release evidence requires the unified ordered build under the research branch policy.
