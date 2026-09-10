# Selected regular layer-cake instantiation

Checked source: [SelectedRegularLayerCakeInstance.lean](experiments/SelectedRegularLayerCakeInstance.lean).
Focused NUC v2 is GREEN: exit 0, 4.82 seconds, peak RSS 6,889,564 KiB,
zero swaps, ten standard-only axiom audits. The source review used the green
predecessors committed at `ff600147c34cf6fcc7946c54c42cfc818279ce54`.
No frozen predecessor was edited. The parent ran both capped Tailscale NUC
checks; this agent verified the copied source snapshots, logs, manifests
and green output locally. The checked source is now frozen.

## Constructed source tables

For one fixed received/OOD execution, common row r and polynomial Z, define

    factorEvent(F,gamma,kappa,tau,alpha) :=
      Z(gamma) != 0 AND Retained(F) AND lowRegularPrefix(F,gamma,kappa,tau,alpha)
    Active(F,gamma) := exists kappa,tau,alpha, factorEvent(...).

Retention is for this SAME F. `lowRegularPrefix` alone does not imply it:
its low higher-prefix witness could involve a different factor. Membership
and degree at least three come separately from the actual `higherFactors`
multiset at each summation occurrence. Repeated factors are not discarded.

`representative` chooses one Qualified Q on an active pair and is zero on
an inactive pair. Its support table is the actual complete-fibre support
of Q when active, and explicitly zero otherwise. No image or qualification
claim is made about the zero placeholder. The choice depends on gamma and
the fixed strategy as a whole, but not on a realized kappa/tau/alpha.

`representative_final` uses the checked `fixed_regular_final` uniqueness
interface to identify every actual final on the same event with that Q's
alpha fold. `representative_bounds` identifies the chosen Q with the
same-factor low witness and derives the literal interval [9558,200807].
This preserves the actual adaptive final, not an adversary restriction
to a pre-alpha final. No polynomial dependence of Q on gamma is asserted.

## Exact moment and tail adapters

`score_moment` instantiates `low_regular_moment` with this constructed Q,
then rewrites the actual query probability through `full_query_mass`:

    mean_A score(F,gamma,.)
      <= if Active then beta(s)+(1-beta(s))*min(1,3/|A|) else 0,
    beta(s) = choose(s,q)/choose(262144,q).

Inactive scores are identically zero. Gamma values at roots of Z also have
zero scores; they remain in the original averaging domain and denominator.
Neither gamma nor alpha is conditioned on the selected event.

`table_tail_le` proves, per factor, the explicit finite-set inclusion into
`supportGammas(...,4*m-2)`, using the same Q, actual source support transfer
and actual row derivative. It sums these cardinalities with multiplicity.
`table_tail_bound` consumes `SelectedRegularTailSum.tail_sum_bound` to give

    H(m) <= B(m) := floor(1048576*239599331/(4*m-1026)), m >= 9558.

Here H is the sum of factor/gamma incidences, not their union cardinality.
The denominator comes from the sharp TWO-SYMBOL loss:
`(4*m-2)-1024=4*m-1026`. It is positive on the integration interval.
No count-of-factors multiplier is introduced.

`factor_moment_bound` feeds all three derived adapters into
`GenericRegularLayerCake.factor_gamma_alpha_conservative`, yielding

    Budget = (1-epsilon)*layer(beta,9558,200807,B)/|Gamma| + 3/|A|.

The explicit hypothesis `6752623450 <= Gamma.card` discharges B(9558)
against the unchanged gamma domain; it is not automatic for arbitrary
finite subsets. For the intended full nonzero QM31 domain it follows from
the existing cardinality theorem, but this draft does not enumerate or
normalize that field, or claim a new source sampler law. It separately
requires Gamma and A nonempty, q<=262144, checked OOD data, both circle
equations and the actual non-west coordinate conditions.

## Union and common-row endpoints

`union_score_le` supplies the explicit nonnegative witness union bound.
Different factors may cover the same prefix; the actual union score is
at most their multiset sum. The tiny `Generic.averaged_union_le` commutes
only finite sums and averages, not marginal probabilities.
`union_moment_bound` bounds the gamma/alpha mean at every fixed kappa,tau.
Its right side is independent of both later history values.

`guarded_low_regular` is a source event inclusion: from literal LowPrefix
and the common-row guard outside Z-roots, it uses `witness_image` and the
same actual Q/factor/final to construct `regularLowUnion`. It does not
assume an already-regular witness for the actual low event.

`exists_common_row_bound` consumes `CommonRegularRow.selected_common_row`.
Outside the full pre-OOD product's pair-root event, it constructs r,Z with
Z nonzero, degree at most 117049 and at most 117049 roots in the original
Gamma, then gives the source inclusion and moment bound for all kappa,tau.
The finite Gamma is fixed before this existential. If a uniform result
over subsequently chosen Gamma subsets is wanted, the predecessor's
Gamma-independent `common_row` must be used instead.

## Explicit remaining integration

This leaf does NOT average or charge the Z-root event, dispose of the
pre-OOD pair-root alternative, or add suffix repairs. The following remain
separate, small source-integration steps:

- Average the kappa/tau-independent Budget and commute the finite means
  into the execution's actual gamma/kappa/tau/alpha order.
- Use `SelectedRegularLowSupport.shared_suffix` on the whole regular-low
  UNION once, retaining its q/|G|+18/|A| term. Do not sum that repair over
  factors or over the representative supports.
- Charge the single Z-root set over the unmodified Gamma domain, alongside
  the already separate high-support and pre-OOD pair-root branches.
- Connect any resulting finite experiment to the actual sampler/ROM law;
  labels alone do not discharge freshness.

The fixed early C1 and actual degree-two helper/full degree-28 claim setup
remain in the underlying execution. This low-branch theorem does not need
or infer a successful early decoder; that premise belongs to the separate
high-support count. No global soundness, authentication, extraction or
payment conclusion is claimed.

## Falsification checks retained

Two factors can cover different three-element alpha sets at one gamma,
giving a six-element union. A single 3/|A| correction is justified only
after the SUM-incidence bound H(9558)<=|Gamma|, not by the gamma union's
cardinality. Likewise, root exclusion cannot renormalize Gamma, and an
event-supported matching mean is not the product of its gamma marginal
and a separate query marginal. The source tables and theorem hypotheses
above exclude these invalid shortcuts explicitly.

## Verification and retained failure

| Attempt | Exit | Wall time | Peak RSS (KiB) | Swap | Status |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 4.64 s | 6,856,280 | 0 | Retained diagnostic; no release credit |
| v2 | 0 | 4.82 s | 6,889,564 | 0 | All ten audits standard-only |

V1 destructured the `active` and `selected` proofs, then referred to their
old names. Its score simplification also retained a redundant conjunction.
V2 destructures copied witnesses and proves the score-indicator equality
pointwise using the fixed nonroot and same-factor retention facts. No
theorem hypothesis, conclusion, numeric budget or compiler limit changed.
The recursion diagnostics in v1 were cascading elaboration failures, not
evidence that a larger resource limit was needed. Failed-run `sorryAx`
audit entries are retained as diagnostics, never counted as proofs.

All ten v2 declarations report only `propext`, `Classical.choice`, and
`Quot.sound`. Both checks used Lean 4.32.0, `-j1 -M9500`, declaration depth
200 and 250000 heartbeats; cgroup MemoryHigh=8589934592,
MemoryMax=10737418240, MemorySwapMax=0, CPU quota=200%. The frozen cached
overlay passed all 967 source/output checks before and after v2. Its
inherited research pin is `289d7356c78a4cd493fe61a54f9548f2a0c11298`,
and borrowed V7 source pin is `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
These cache pins are distinct from the new source parent above. No cold
dependency or package-wide replay was performed.

Exact SHA-256 evidence:

- Frozen source and v2 snapshot:
  `00e09c11c7079bb0d6edcec3cc54f5c7548fa7c447a52870b620df6f7f6b0812`.
- Green output:
  `88f52a711f8f877a190d4aa5a972ae1032495d5d4c115d8979cd56a6a2a75cb1`.
- V2 manifest:
  `99fba856417cdb1e64e9b6edc9a8528dc50c19df9a73bd31b8ce32b07abbd725`.
- V2 log:
  `a277adc501af2e850e6b5eb9615b8707b81be28bd9031625f40499f7a6ca3fdb`.
- V1 snapshot:
  `c59ef0c8b7da5d5ee647ee544cbb536c5bb58343302393b3ada423cd7d458578`.
- V1 manifest:
  `bfe7a63f7effb33bfb551b0e56b76a6325814329181ed494ceb6ce792f9fb37a`.
- V1 log:
  `4bd7b6d4af332e8a3ad6eea23e2dbc15d492f1539d44c8d7918350d1479beb77`.
- Frozen runner:
  `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The two exact attempt triplets are
`experiments/selected-regular-layer-cake-instance-nuc-v{1,2}-{source.txt,manifest.json}`
and the corresponding `.log` files. The ignored `.olean` is a locally
verified cache artifact; reproducible evidence retains the frozen source,
runner, logs and per-run manifests.
