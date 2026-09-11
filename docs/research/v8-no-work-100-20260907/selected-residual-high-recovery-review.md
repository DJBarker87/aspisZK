# Selected high residual: checked same-Q event bound

Status: GREEN on the first focused NUC run. Target:
[SelectedResidualHighRecovery.lean](experiments/SelectedResidualHighRecovery.lean),
SHA-256 `2924bf616df3fdaefd952b61f4ee78c61ef961d605cc7407282692c41b133abc`.
All nine axiom audits passed with standard axioms only and no `sorryAx`.
The proof source and checked image-recovery predecessor are unchanged.

## Event and checked interfaces

`RecoveredHigh e family gamma kappa tau alpha` means there is one Q carrying
all three facts:

- The actual `SelectedHigherYHighSupport.Witness`, including its literal
  quotient-family membership, image/ordinary-row gates, old higher root,
  and equality to the final selected after tau/alpha.
- `HighSupport (e.raw gamma) Q`, the exact quotient fibre-bad threshold
  `≤4*15334`, equivalently at least 200808 full matching fibres.
- `SelectedMiddleImageRecovery.Recovered` for the SAME Q and the supplied
  fixed family: own support at least 38228, original(Q)=batch(gamma,p), and
  the same p's C1 projection in the fixed EarlyC1Family.

`recovered_high_implies_high` projects the actual HighPrefix, so this is a
valid recovered predicate for the separate high/LOW residual composition.
It does not mean that recovery alone proves payment or terminal acceptance.

`high_recovered` consumes one fixed family/E/beta/sparse classification and
an explicit bad Finset equal to its shared/sparse/insufficient-own union.
Outside the SAME E pair-root event and outside bad, it derives RecoveredHigh
from HighPrefix. The proof uses
`SelectedAcceptedPrefixPartition.high_same_quotient`, restores HighSupport
for that returned Q with `full_bad_partition`, applies the checked
`candidate_outcome`, and eliminates its impossible pair/exception cases
through a field-free propositional helper. It does not select a different
quotient for the row/image and reconstruction parts.

The residual mass is exactly

```
avg Gamma (gamma ↦ avg G (kappa ↦ avg G (tau ↦ avg A (alpha ↦
  if HighPrefix e gamma kappa tau alpha ∧
     ¬RecoveredHigh e family gamma kappa tau alpha
  then actualSuffix e gamma kappa tau alpha A G else 0))))
```

This is the same unfolded high-residual expression used by the separate
composition work, with its arbitrary recovery predicate specialized. The
leaf does not import the separate composition leaf. A later transport
can unfold only the two probability definitions if required.

`high_residual_card_bound` bounds this expression by bad.card/Gamma.card.
Its recovery premise is uniform over all later kappa/tau/alpha histories.
`high_residual_probability_bound` discharges that premise with
`high_recovered` and uses the checked `selected_exception_card` to obtain
`104/Gamma.card`. The pointwise bound uses `after_unit` on the actual suffix;
there is no scalar acceptance replacement or second suffix repair.

## Exact supplied premises and fixing order

Imports are only the checked `SelectedMiddleImageRecovery`,
`SelectedAcceptedPrefixPartitionV2`, and `SelectedHigherYProbability`.
The bound supplies family.card≤1, beta≠0, beta.natDegree≤40,
sparseSource.card≤28, the exact bad-set equality, `CandidateClassifies`,
checked OOD data, both circle equations, both west-pole exclusions, and
nonempty A/G with q≤262144. It explicitly excludes PairRoot E e.data.

The existing `MiddleLinearClassification.exists_classification` supplies
the algebraic prefix existence separately. The new theorem does not
postselect a family/bad set for each gamma or later history: all are fixed
arguments before the original gamma average. C1/C2 and E precede both OOD
points; beta may depend on completed OOD data/answers before gamma. Q and
the strategy final remain adaptive after later challenges. This leaf does
not require earlyC1=some, earlyC1=none, regularity, a nonzero gamma, or
polynomial received words. Gamma is not renormalized to its good subset.
The empty-Gamma rational-mean convention remains valid; no positive-Gamma
premise is needed for this cardinality bound. The source execution's actual
sampler distribution is not inferred from the notation `avg`.

## Small exact falsification checks

The implication is deliberately limited to the high residual. At the
pointwise indicator interface, `HighPrefix ∧ RecoveredHigh`, suffix one and
gamma outside bad are not excluded: deleting `¬RecoveredHigh` would then
turn the desired indicator bound into `1≤0`. This is a propositional
saturation test, not an assertion that an honest selected higher-prime
execution realizes HighPrefix on every gamma. Allowing a different bad set
after observing gamma is also unsound: every gamma can be put into its own
singleton while each chosen set has cardinality one. The fixed-set
quantifiers prohibit this strategy.

No new improvement is assumed for the saturated LOW moment gate. A high
witness's mere acceptance does not imply the image/support hypotheses;
here they come from the explicit HighPrefix witness and the checked source
bridge. The earlier causal gamma=1 empty-family control is not contradicted:
it can remain exceptional, and the result keeps pair-root histories out of
this conditional bound. Image recovery's fixed degree-28 error budget and
degree-two helper timing are reused unchanged.

## Remaining boundaries

This leaf is an event/mass adapter, not a total accepted extraction proof.
No-good/no-factor/lower/LOW accounting, the recovered branch's same-tuple
claims and semantic/payment authentication, and any OOD/FS freshness law
remain separate. One can next compose this high residual with the checked
LOW bound, spending its repair only once, outside the product of the same
middle obstruction and the singular obstruction. That composition is not
asserted proved by this leaf.

Module limits remain depth 200 and 250000 heartbeats. There is no local
increase or broad reduction of selected domains. Proofs are split into
the same-Q event inclusion, a pointwise indicator, a generic finite-mean
bound, and the final numeric-card consumer. No proof edits or further build
are required for this checkpoint.

## Exact first-run evidence

Tag: `selected-residual-high-recovery-nuc-v1`. Exit 0; wall 3.99 seconds;
peak RSS 6,885,032 KiB; swap 0. Pre/postflight provenance passed with 1073
entries, unchanged. The log contains nine exact requested declaration
audits; each uses only a subset of `propext`, `Classical.choice`,
`Quot.sound`, and `Generic.outcome_recovered` uses none. There are no
warnings, errors, or `sorryAx` entries.

Evidence: [source snapshot](experiments/selected-residual-high-recovery-nuc-v1-source.txt),
[build log](experiments/selected-residual-high-recovery-nuc-v1.log),
[immutable manifest](experiments/selected-residual-high-recovery-nuc-v1-manifest.json).

| Artifact | SHA-256 |
| --- | --- |
| Live source and snapshot | `2924bf616df3fdaefd952b61f4ee78c61ef961d605cc7407282692c41b133abc` |
| Green olean (logged remote digest) | `b59a375f064d6292d619d7ce825eb4768344662fb7f40d0061f72907a21b8bf4` |
| Manifest | `36147cec5c1b0b78f86b941cbc9f9e9ee633db541f61e076b8a9412608b814c6` |
| Log | `43b51ab16f4d7ee0f2b87b0acbc4b1f6cc055767de8b2534dd466650391aeb7d` |

Research source parent: `7c8e18488f1337b1ff247908a1a8e86325ec29bb`.
The inherited NUC runner/cache research pin remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, with borrowed V7 source
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Lean 4.32.0 commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35` ran only this target through
Tailscale in the established scope: `-j1 -M9500`, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax zero, CPU quota 200%.
The [frozen runner](experiments/run_higher_y_nuc.sh) hash is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
No package replay, new cache variant, larger resource cap, or unchanged
retry was used. Local closeout verified the exact source/snapshot, log and
manifest hashes, the recorded remote output digest, and all nine audit
names/axiom sets. The olean binary was not copied or committed for this
closeout; its digest is evidence from the successful remote log, not a
claim of an independently hashed local binary.
