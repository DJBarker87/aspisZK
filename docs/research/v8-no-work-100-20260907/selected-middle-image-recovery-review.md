# All-image high-support recovery: checked theorem chain

Status: `SelectedMiddleImageRecovery.lean` V16 is GREEN. This is a theorem
chain, not a checked monolithic `exists_recovery` package. The retained
[source](experiments/SelectedMiddleImageRecovery.lean) exports the candidate
classification, exception cardinality, and exception subset as separate
opaque facts. The prefix existence theorem is reused, not reproved.

## Exact result and causal fixing

`SelectedMiddleSimpleParent.parent c1 c2` is fixed by the received C1/C2
words before either OOD point. Its nonzero interpolation kernel, Y-degree
at most one, and candidate-root theorem apply to any image-valid quotient
with at least 200808 full matching fibres. This does not identify the
unrelated old `fixedInterpolant` choice with a hand-picked kernel element.

Instantiate `MiddleLinearClassification.exists_classification` with this
parent. It supplies the same nonzero pre-OOD obstruction E of degree at
most 65061549, a fixed tuple family of cardinality at most one, a sparse
gamma set of cardinality at most 28, and, after the OOD points and answers,
a nonzero beta of degree at most 40. Its candidate classification is exactly
the premise named `CandidateClassifies` in the new leaf. These existence
facts must be supplied coherently; the leaf does not choose a new E, family,
or plan for each candidate.

For that same family/beta/sparse source and the original finite Gamma, set

```
bad = (Gamma ∩ roots(beta))
      ∪ (sparseSource ∩ Gamma)
      ∪ ⋃ p∈family, insufficientHits(p).
```

The checked `selected_exception_card` proves `bad.card ≤ 104`, and the
separate `selected_exception_subset` proves `bad ⊆ Gamma`.
`candidate_outcome` applies to every gamma in Gamma and every SAME Q with
the two image equations and at least 200808 full matching fibres. Its
`Generic.Outcome` has explicit, disjoint precedence:

1. Both OOD points are roots of the same E.
2. Outside that pair-root event, gamma belongs to bad.
3. Outside both events, `Recovered` holds for this same Q: there is a p in
   the fixed family with own-symbol support at least 38228,
   `original(Q) = batch gamma p`, and
   `c1Projection p ∈ EarlyC1Family.family c1`.

Q is universally quantified after gamma and may be the quotient selected
through later kappa/tau/alpha and the adaptive final. No gamma-polynomial
dependence of that selection, old higher-factor root, regularity, ordinary
row correctness, early-C1 success, or own support is assumed. The OOD data
remain checked, both circle equations hold, and both points avoid the west
chart pole; these are explicit hypotheses. C2 may depend on earlier
semantic challenges, but C1/C2 are fixed before this OOD experiment.

## Why the exception is 104

`matching_of_image` transfers full-fibre support of the same Q to at least
`4*200808-2 = 803230` original-symbol matches. The two-symbol loss is kept;
no globally pole-free received word is assumed. `image_points` derives the
two exact OOD polynomial evaluations from the source image equations.

For a fixed tuple with own support b below 38228, the reused
`MiddleCoherentIncidence.Generic.small_own_card_le_36` gives

```
|G| * (803230-b) ≤ 28 * (1048576-b), hence |G| ≤ 36.
```

At the limiting integer b=38227, 37 gammas exceed the incidence budget by
15339. These are fixed degree-28 component error polynomials, not a claim
that a postselected candidate curve has degree 28. The fixed family has
size at most one, so the conservative union is `40+28+1*36 = 104`.
The sets may overlap; no disjointness or independent challenges are used.
The three helper lanes still have degree two. They are not silently
replaced by the 29-lane degree-28 error polynomial.

This auxiliary tuple family is not the C1-only family of size at most 100;
there is no blind 100-target union. `earlyC1 = none` also does not mean that
the weaker `EarlyC1Family` is empty: the option uses a different, stronger
full-fibre threshold. The recovered alternative is therefore meaningful
even when that option is none.

## Remaining source/event and extraction obligations

The new result bounds failure of this recovery classification, not the
probability of all acceptance or of payment failure. The next event adapter
must retain the actual witness from
`SelectedAcceptedPrefixPartition.high_same_quotient` and identify its
HighPrefix image/support hypotheses with this same Q. It can then remove
the recovered high event and charge only bad gammas, with the actual suffix
bounded by one. No average or such accepted-event adapter is in this leaf.

`SelectedAcceptedPrefixPartitionV2` partitions the existing ideal compact
relation event, not literal Rust verification. No-good/no-factor/lower/LOW
branches remain separate. No-good includes outside-family, nonzero-prior,
and first-collision alternatives; it cannot be relabeled image-valid HIGH.
The recovered event itself still needs same-tuple point-claim/semantic and
payment transport. Commitment-to-word authentication, initial-mask and
terminal-opening authentication, base-field/source coupling, and a bounded
extractor are not discharged here. Neither stopped-prefix nor nested-fork
results establish them. Pair-root averaging additionally needs the explicit
history-uniform OOD law; no Fiat--Shamir freshness is asserted.

The earlier 97.1879-bit naive extension of the regular LOW screen is not a
new probability claim here. Existing middle-parent gamma classification
already offers a different HIGH higher-Y route; this leaf strengthens the
all-image recovery alternative and leaves the recovered branch live.

## Permanent falsifier checks

The existing fixtures/reviews were checked for compatibility, not rerun
unchanged:

- [Moment saturation](no-early-middle-moment-obstruction-review.md): with
  zero prior, compatibleMoment is exactly matchingRatio. The missing
  approximately 7.07 factor is not obtained from that gate.
- [Row-qualified middle control](row-qualified-middle-obstruction-review.md):
  training-node interpolation and ordinary rows do not force fresh-node
  coherence; fixing OOD points retrospectively is not a causal strategy.
- [Empty early-family kernel control](empty-early-family-kernel-control-review.md):
  the causal gamma=1 high-support example is consistent with a bounded
  exception; its membership in a hand-chosen interpolation kernel is not
  membership in the literal selected interpolant.
- [Selector dimension audit](initial-interpolation-selector-gap-review.md):
  projective one-dimensionality cannot be assumed. The new auxiliary
  linear-Y parent derives its root property for its actual selected kernel
  vector instead.

The new fixed-family construction does not assume that eight holdout
gammas agree with a tuple interpolated from 29 selected nodes. Singular,
repeated-factor and degree-drop cases remain accounted for by the reused
linear classification's beta/sparse/E alternatives.

## Focused build evidence and resource repair

Research source parent: `7c8e18488f1337b1ff247908a1a8e86325ec29bb`.
Inherited runner/cache research pin:
`289d7356c78a4cd493fe61a54f9548f2a0c11298`; borrowed V7 source pin:
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The exact [runner](experiments/run_higher_y_nuc.sh) SHA is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`,
was run through the existing Tailscale NUC scope, one target at a time,
with `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB, SwapMax zero,
and CPU quota 200%. No package replay or larger memory cap was used.

Each attempt's immutable source, log and manifest is retained under
`experiments/selected-middle-image-recovery-nuc-vN-{source.txt,manifest.json}`
and `experiments/selected-middle-image-recovery-nuc-vN.log` for N=1..16.

| Version | Exit | Wall seconds | Peak RSS KiB | Swap | Result/change |
| --- | ---: | ---: | ---: | ---: | --- |
| 1 | 1 | 3.94 | 6848852 | 0 | Finset argument order and selected elaboration |
| 2 | 1 | 4.15 | 6852480 | 0 | Generic helpers green; nested membership depth |
| 3 | 1 | 4.16 | 6852664 | 0 | Scoped-option/doc parser seam |
| 4 | 1 | 4.13 | 6852996 | 0 | Declaration keyword change did not fix parser |
| 5 | 1 | 4.16 | 6852920 | 0 | Doc placement/scoped-option seam |
| 6 | 1 | 4.23 | 6852776 | 0 | Local depth 400 insufficient |
| 7 | 1 | 4.23 | 6854700 | 0 | Local depth 1000 insufficient |
| 8 | 1 | 4.49 | 6858928 | 0 | Bounded local depth 2000 diagnostic insufficient |
| 9 | 1 | 15.49 | 9728596 | 0 | Decision-instance mismatch and kernel memory |
| 10 | 1 | 15.77 | 9728868 | 0 | Concrete-set helpers fixed mismatch; aggregate memory |
| 11 | 1 | 15.55 | 9728588 | 0 | Selected inductive memory and Prop-to-Type elimination |
| 12 | 1 | 15.64 | 9730488 | 0 | Generic outcome fixed elimination; monolithic memory |
| 13 | 1 | 15.52 | 9729848 | 0 | Candidate green; aggregate data theorem memory |
| 14 | 1 | 15.57 | 9728952 | 0 | Proof-only structure still aggregate memory |
| 15 | 1 | 15.73 | 9730312 | 0 | Aggregates removed; card/subset conjunction memory |
| 16 | 0 | 4.85 | 6887052 | 0 | Separate card and subset facts: all 27 audits green |

The failed aggregate declarations were removed, not replaced by `sorry` or
additional assumptions. The retained chain has three opaque consumption
boundaries: existing prefix existence, new card/subset facts, and the new
candidate outcome. Concrete Finsets avoid hidden decision-instance
equalities. `candidate_outcome` alone retains declaration-local depth 1000
for static selected-interface elaboration; all other declarations use the
module depth 200. Heartbeats remain 250000. No failing resource-heavy term
was retried unchanged with a higher memory cap.

Final evidence: [V16 source snapshot](experiments/selected-middle-image-recovery-nuc-v16-source.txt),
[V16 log](experiments/selected-middle-image-recovery-nuc-v16.log),
[V16 manifest](experiments/selected-middle-image-recovery-nuc-v16-manifest.json).
Pre/postflight provenance: 1069 entries, unchanged. The log has 27 exact
`#print axioms` outputs: only subsets of `propext`, `Classical.choice`,
`Quot.sound` (the generic Outcome has none); no `sorryAx`. Unused-variable
lint warnings remain and are not proof failures.

| Artifact | SHA-256 |
| --- | --- |
| Live source and V16 snapshot | `476bf9754cc379534b21a4c0067b774a46bd6c82e234222c7644c7f678a2887c` |
| Green olean | `2479826310ddcbc8770268be525dabacbe8c9dd862369e2d58b971d223761653` |
| V16 manifest | `d388e56b15f6d1c96a90fe94d7c192db49068ae96f1963d9519ea83f5d413d70` |
| V16 log | `5646a05708aefc1065f5db4216f0e6d8b539213ec76518b2eb0882cd2c90cf84` |

Local closeout verified all 16 source/manifest hashes against their logs,
the final source against its snapshot, the green output against its logged
hash, and the exact 27 requested declaration names and axiom sets. No
unrelated stopped-prefix, termination, component-claim or composition file
was changed by this closeout.
