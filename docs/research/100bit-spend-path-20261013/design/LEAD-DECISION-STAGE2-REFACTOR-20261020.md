# Lead decision: source-preserving refactor of stage 2 for extraction (2026-10-20)

Finding (`STAGE2-EXTRACTION-20261020.md`, cx-stage2 546c8fa94): the frozen
`finish_relation` (body SHA 11d1e3f6…) fails the pinned Charon/Aeneas
pipeline; `resume`'s mutable `Reader`/`from_fn` closure and the post-finish
`Accumulator` borrowing fail as well. The stage-2 cone is 76 declarations
and 16 closures, 66 shared with the adopted tx1 cone, 10 stage-2-only.

Decision: take the refactor route used for stage 1 (Decisions 1–1h), not
tool work. A source-preserving refactor of `finish_relation` (starting from
the retained candidate `lean-candidates/finish-relation-source-candidate-20261019`:
shallow scalar fold-guard helpers, specialised one/two rounds, an indexed
final dot over shared slices), of `resume`'s reader (closure replaced by an
explicit indexed reader) and of the accumulator borrow, each the smallest
change that translates. Gates, all required: codec 1,233 byte-identical,
ordered trace, checkpoint tests, Pool suites, strict stack audit, the
proof-size teeth, P_R1 retrying prover ≥ 8/8, and the six-fixture CU within
`PREREG-PROOF-SIZE-2` item 1 (stage 1 ≤ B1, settlement ≤ B1 + 10,000). The
source freeze (`LEAD-REVIEW-FORMAT-ADOPT-20261020.md`, amended by
`LEAD-DECISION-DEPLOYMENT-IDS-20261020.md`) is amended to the post-refactor
revision; the stage-2 CU re-pins (S8) and the CU bound are re-run on it. The
refactor is a verifier source change and is labelled as such in every
packet.
