# Residual prefix classifier: focused Lean result

Status: focused NUC replay passed. New target:
[SelectedResidualPrefixClassification.lean](experiments/SelectedResidualPrefixClassification.lean),
SHA-256 `e8a8c52f614e9ed14380bafe28b2e998ad7e1105c872fba125b5cc1777589aba`.
Research parent: `eb06c838bdeb002508dac2b4af406631f3d67e66`.
All three axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx`.

## One real hypothesis removed

The first remaining obligation in [residual-recovery-closure.md](residual-recovery-closure.md)
groups several distinct interfaces: source-to-Execution, CandidateClassifies,
checked OOD data, and the terminal event. CandidateClassifies itself does
not require parsing, authenticated commitments, honest received words, or
a successful recovery provider. It follows from the existing actual C1/C2
auxiliary interpolation parent and the checked linear-factor theorem.

The proposed `exists_source_classifier` derives, for any C1/C2 and fixed
finite Gamma:

```
∃ E ≠ 0, degree(E) ≤ 65061549,
  family(c1,c2).card ≤ 1,
  sparseSource(c1,c2,Gamma).card ≤ 28,
  ∀ Data d, ∃ beta ≠ 0, degree(beta) ≤ 40,
    CandidateClassifies c1 c2 Gamma family E beta sparseSource d.
```

The family is literally `LinearMessageFamily.family` of
`SelectedMiddleSimpleParent.parent c1 c2`, and sparseSource is that same
parent's `sparseChallenges`. Neither is a supplied target family or a
family selected after gamma. E precedes both OOD points; beta is selected
after the completed OOD data but before every gamma/message continuation.
The returned SAME E must be used in the residual product/pair bound. The
proof does not identify it with an independently chosen E elsewhere.

Thus the classifier, family-cardinality and sparse-cardinality hypotheses
of `SelectedResidualRecoveryBound.conditional_nonpair_bound` can be derived
for its actual received C1/C2. Its bad set can be defined as the already
checked explicit union. No new probability or numeric error charge is
needed. This leaf does not reproduce the failed monolithic own-support
recovery package; it stops at the small source classifier interface.

## Exact dependency and variable-map audit

Only `SelectedMiddleImageRecovery` is imported; all other dependencies are
already in that green closure. The proof has three opaque boundaries:

1. `Generic.exists_row_plan` reuses
   `MiddleLinearClassification.exists_classification` at an abstract parent
   P. Its nonzero/Y/X/weight hypotheses are unchanged. The generic predicate
   retains the complete two-row, degree-28 answer and root implication.
2. `row_plan_candidate` inserts exactly `SelectedOODGate.point d` and
   `CurveOODGate.answerCurve (answers d r)`. The degree premise is derived
   from `answerCurve_degree`, not assumed. The resulting statement is the
   literal `SelectedMiddleImageRecovery.CandidateClassifies`, including
   its exact `challengeCandidateHom`, GRS encoding and batch equality.
3. `exists_source_classifier` derives the hypotheses from
   `SelectedMiddleSimpleParent.parent_nonzero` and `parent_bounds`:
   Y-degree≤1, X-degree≤803229, YZ-weight≤40. No old selected factor or
   parent equality is asserted.

This reuses the pinned V7-derived trivariate factorization, normalized
GRS conversion, interpolation root, and weighted factor budgets already
consumed by the green parent/classification leaves. No new old-schedule
module or broad V7 cache replay is requested.

The classifier exists even for unchecked Data. Actual image-Q candidates
need checked data and circle/chart guards to prove its root and OOD-value
premises, as already done in `candidate_outcome`; those guards are not
silently discharged here. A classifier implication whose root/point
premises do not hold may be vacuous, which is why source-event transport
must still preserve its actual candidate.

## Falsification and causality checks

Allowing beta or the tuple family to depend on the realized gamma would
make a small root-cardinality statement useless: each realized value can
be placed in a newly chosen singleton. The universal gamma/message
quantifiers are inside CandidateClassifies and follow the existential
beta, so this change is not permitted. E is also outside universal Data,
not selected after either OOD point. Gamma is fixed as an experiment
domain before these choices.

No step infers a component tuple from 29 self-selected training nodes,
asserts the other nodes are coherent, or equates a hand-picked kernel
vector with the literal interpolant. The new parent is the already
constructed auxiliary parent with derived nonzero and degree properties.
The degree-two helper lanes remain distinct from the degree-28 claimed
answer/error polynomial. The actual Q/final is still allowed to depend
on later gamma/kappa/tau/alpha through the universal candidate implication.

## Source-to-Execution still open

Read-only inspection of tracked `TypedRelationTerminalV3` found
`Fields.strategy`, causal decoded-buffer projections at the selected
697-field offsets, and `source_accepts_iff`. These prove a source-shaped
field-callback acceptance equality. `OptimizedRelationRefinement` derives
compact six-field recurrence boundaries and its repair game; it is not an
Aeneas execution theorem. Both explicitly leave authentication and an
actual Rust transcript-to-callback/Execution construction open.

Consequently this leaf does not manufacture total C1/C2 received words
from commitments, prove Checked/circle/chart conditions from parsing,
discharge terminal or initial-mask authentication, infer ordinary-row
correctness from a scalar aggregate, or prove the repaired verifier's
acceptance equals the ideal event. It also does not construct an efficient
extractor or supply ROM/FS freshness. Those are genuine remaining parts
of the closure report's first and subsequent obligations, not aliases for
CandidateClassifies.

## Focused verification evidence

The retained successful command used Lean 4.32.0 with `-j1 -M9500` in a
systemd scope capped at MemoryHigh 8 GiB, MemoryMax 10 GiB, SwapMax 0 and
CPUQuota 200%. Exit status was 0, wall time 3.08 s, peak RSS 6,870,984 KiB,
and swaps 0. The source and output hashes are recorded in
`experiments/selected-residual-prefix-classification-v2.log` and its frozen
manifest/source companions. This was one focused leaf, not a package replay.
