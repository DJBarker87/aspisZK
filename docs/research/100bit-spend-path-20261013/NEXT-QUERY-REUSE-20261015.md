# Existing query-bound reuse for the next step

This note inventories checked query-counting and repeated-fold/list results.
It records reusable statements and their assumptions; it does not instantiate
a different sampler or make a protocol-security claim.

## Query sampling and cardinality

`R0C.QueryCounting.subset_mean` in
[`QueryCounting.lean`](../v8-r0-close-20261007/lean/R0C/QueryCounting.lean)
is the most general checked counting identity found. For arbitrary `q`, a
finite type `A`, and `M : Finset A`, it states that the uniform mean over
ordered injective `q`-tuples in `A` of the indicator that every tuple element
belongs to `M` equals
`(M.card.choose q : ℚ) / (Fintype.card A).choose q`. Its premises are finite
cardinality and decidable equality for `A` (plus finite instances for the
ordered-injection subtype); it is a counting identity, not a theorem about
the implemented q22 sampler.

[`AspisR0.QueryLaw.uniform_subset_bound`](../v8-wide-reference-20261005/lean/R0/QueryLaw.lean)
allows arbitrary `q` with `q ≤ 262144`, but fixes the domain to
`Fin 262144` and assumes `M.card ≤ 9557`. It gives the exact uniform-subset
ratio and the upper bound
`C(9557,q)/C(262144,q)`. It does not identify that uniform subset law with
another protocol sampler.

The actual retained sampler result is fixed to q22. In
[`QuerySource.lean`](../v8-r0-close-20261007/lean/R0C/QuerySource.lean),
`R0C.QuerySource.successful_subset_exact` and
`successful_subset_le` concern the 8-step `Q22SamplerProgram` on
`Fin (2^18)`. The exact successful-event mass is the sampler's success mass
times `C(M.card,22)/C(262144,22)`; exhaustion contributes zero in the
unconditional bound. [`Q22Law.lean`](../v8-r0-close-20261007/lean/R0C/V3/Q22Law.lean)
packages the fixed-support case as `R0C.V3.Q22.q22_bound`: for
`M.card ≤ 9557`, the 8-step q22 chain's successful 22-set containment event
has mass at most `C(9557,22)/C(262144,22)`.

R1's `BoundedQueries.no_claims_bounded_q22`,
`RawQueryBound.raw_no_claims_bounded_q22`, and
`MatchingSupport.no_claims_ideal_q22_bound` retain this fixed 22/262144/9557
envelope after deriving a no-claims support cap. The R1 query-law bridges
(`QueryNextBound` and `UnifiedQueryLaw`) transfer an explicit fixed-context
bound; they do not derive a new bound for a different q or domain.

The existing [`FS-BUDGET-PROFILE.md`](FS-BUDGET-PROFILE.md) records an exact
rational q-sweep from 22 through 40. At q=23 the semantic row becomes the
largest coefficient, so increasing query count alone does not materially
raise the combined raw margin; the sweep reports that parameter-only changes
do not reach a total `2^-100` bound under its fixed-row assumptions. This is
ledger arithmetic, not a new sampler theorem or a full-experiment query
bound.

## Repeated-fold support and list size

The current two-fold extraction route is
[`TwoFoldExtraction.two_fold_extract`](lean/TwoFoldExtraction.lean). Given
at least 9,558 matching positions in `Fin 262144` and the explicit challenge
exclusions and matching equations, it uses the second-fold matched theorem
and first-fold restoration/matching to produce a message tuple in the literal
list `Lambda W`. `ParentSupport.parentSupport_card_ge_2390_*` records the
intermediate conversion to at least 2,390 distinct parent positions. This
intermediate support threshold is not itself a list-cardinality bound.

The checked width-29 list cap remains
[`JointList.jointInitialList_card_le_100`](lean/JointList.lean): every family
member must agree jointly on at least 38,230 domain points, and the theorem
concludes the family has at most 100 elements. The partial-lane form
[`PartialJointList.partial_family_card_le_100`](lean/PartialJointList.lean)
zero-pads unselected lanes and preserves the same 38,230 selected-support
threshold; it does not lower that threshold.

[`RepeatedLift.repeated_lift_projection_descent`](lean/RepeatedLift.lean)
has a 64-base-point threshold, yielding 256 repeated coordinates. Its
conclusion is equality with a projection, under explicit hypotheses of
complete four-lane constancy, a projection-mean identity, nonzero four, and a
pairwise overlap cap of 255 for distinct messages. It is a conditional
projection-descent lemma, not a list-size or query-sampling theorem.

These existing results supply reusable counting and support interfaces. They
do not by themselves change the q22 sampler, instantiate the full experiment's
distinct-first-read budget, or close the remaining Fiat–Shamir premises.
