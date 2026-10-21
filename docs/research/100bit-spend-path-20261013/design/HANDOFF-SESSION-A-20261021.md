# Handoff to session A (S-cone re-pins), 2026-10-21

From the lead coordinator. Short version: the soundness headline changed this
morning, and it now asks for something specific and narrow from each S-cone
re-pin.

## What changed

The user approved the oracle-decision port. The headline soundness theorem is
now `OraclePortHeadlineFrozen.final_soundness`
(`lean/OraclePortFrozenOrderHeadline.lean`; addendum "oracle-decision port
ADOPTED" in `design/C3-BIN-20261021.md`). Its only source premise is
`AcceptedRunJoin D rust`: on every run the frozen Rust verifier accepts, its
oracle log and outputs equal those of `dV_frozen`, the Lean model of the
frozen verifier, with the exact frozen multiproof order.
`design/JOIN-SPLIT-DRAFT-20261021.md` proves that this join follows from
per-cone joins plus one ordered caller join.

## What each re-pin should deliver

For each cone you own (S1–S6 and S9 per the user, 2026-10-21; the lead has S7, S8, S10, parser, multiproof, checkpoint ABI and Pool caller), the target is an
**accepted-run refinement against the matching `dV_frozen` stage**: whenever
the frozen function returns successfully on the reached inputs, its result
(and any oracle reads) equal the model stage's. The exact statement shape for
each cone is in the join-split table, and `design/CONE-AUDIT-20261021.md`
classifies what already exists and how close it is. The audit ranks S9 and S3
among the cheapest three to close next; the lead is doing the third, the
checkpoint ABI, plus the parser and multiproof cones.

Please state the refinements in **total form** where you can: for every input,
the extracted function returns `ok v` and v equals the model. Then overflow
freedom (R22) for that cone follows automatically from the lemma in
`design/R22-TOTAL-20261021.md`, and no separate overflow census is needed.

## Integration items

- **Combined import.** Duplicated `instDiscriminantErrorIsize`-style instances
  across separate Aeneas extractions block one aggregate import (10 duplicate
  names; three conflicting). A type-qualified naming fix is prototyped and
  shown to compile all cones together (`design/IMPORT-UNION-20261021.md`). It
  needs the S10 pins updated before the single final manifest replay.

## Two things the lead did that touched your work

1. Commit aab0d23d0 (2026-10-20 ~22:40, "Record R19 discharge…") swept in 23
   of your staged files from `lean-candidates/s5-p6-serializer-kani-v1-20261020/`,
   because we share the root checkout's index. Nothing was lost or altered,
   and your later commits build on them. Authorship is yours; the lead now
   commits with explicit paths only.
2. At about 09:33 the lead killed local ssh PID 33838
   (`ssh … echo <base64> …` writing a script for
   `project-offloads/s5-charon-selfid-repair-v1`). It had been hung since the
   ~08:12 network drop, with nothing running behind it on the host. Your
   separately started build-v5 run was not touched. If something was waiting on
   that command, please rerun it.

## S10 ownership lists for your acceptance (added 11:20)

S10 pass 2 assigned every reachable declaration of the frozen verifier and
Pool to a cone. The declarations it assigned to your cones (S1–S6, S9) are
listed in the S10 evidence (`evidence/s10-inventory2-20261021/`, see
`design/S10-INVENTORY-20261021.md`), with 57 ownership corrections. Please
review the lists for your cones and confirm or correct them. Your proved cone
joins should cover exactly those declarations.

## Target update (13:05)

The model now covers both transactions. The headline is
`OraclePortHeadlineFrozen2PerAttempt.final_soundness`, and its
`AcceptedRunJoin` is stated against `dV_frozen2`: stage 1, checkpoint save,
then Pool stage 2, with the six checkpoint digest reads in place. The
per-cone targets for S1–S6 and S9 are the matching stages of `dV_frozen2`.
For the non-checkpoint stages these are the same as the `dV_frozen` stages,
because only the checkpoint stage was inserted (`design/DV-TWOTX-20261021.md`).
The contract you are proving toward is `design/SECURITY-CONTRACT-20261021.md`:
100-bit per attempt, no grinding credit.

## Dependencies of the lead's cones on yours (23:35)

- **S7** needs the source `four_dots`, opening, fold and geometry joins from
  S4/S5 to finish its whole-function certificate.
- **S8** needs the source EbyKDot and relation-finisher laws, from the S3/S9
  EbyK work.
- **Every** lead cone (multiproof, checkpoint, S7, S8) also waits on S2's caller
  binding.
When these land, the lead composes them; please state their joins against
`dV_frozen2`, in total form where possible.
