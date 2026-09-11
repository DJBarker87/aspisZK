# Residual recovery: exact arithmetic for the checked conditional composition

This is the exact arithmetic record consumed by the focused, kernel-checked
composition chain in `ResidualRecoveryCompositionV8`,
`SelectedResidualHighRecovery`, and `SelectedResidualRecoveryBound`. The
Python arithmetic itself is not theorem credit. The Lean results prove the
symbolic conditional bound and derive its high-residual premise from one fixed
pre-OOD classifier; the remaining actual-source, authentication,
Fiat--Shamir, and payment-extraction interfaces are explicit below.
The arithmetic is independently reproducible by
[residual_recovery_probability.py](experiments/residual_recovery_probability.py);
its complete reduced fractions are retained in
[residual-recovery-probability.json](residual-recovery-probability.json).

For the selected ideal domains, the proposed bound is
`4.930816525590405969786551e-32`, or approximately
`2^-103.999872464867748578`. Exact rational comparison shows it is
**strictly greater than `2^-104`**. This must not be rounded into a claim of
at least 104 bits. No grinding allowance or security credit is included.

## Fixed objects and exact residual event

Fix the SAME C1 and C2 received words before either OOD draw. The new cover
chooses a tuple family `F` of cardinality at most one and a nonzero middle
obstruction `E_m` of degree at most 65061549 before the OOD data. Independently,
`SelectedSingularOODFamily.obstruction c1 c2` is a nonzero polynomial `E_l`
of degree at most 25345827, also fixed from C1/C2 alone. The actual OOD
points and their answer vectors may be chosen sequentially. They precede
gamma; the final remains adaptive after gamma/kappa/tau/alpha.

For a terminal-history execution `e`, define the following proposed event
notation, not new declarations asserted to be present in Lean:

    RecoveredHigh_F(e,g,k,t,a) :=
      exists Q, SelectedHigherYHighSupport.Witness e g k t a Q
        and HighSupport (e.raw g) Q
        and exists p in F,
          38228 <= card(SelectedOwnSymbol.own e.c1 e.c2 p)
          and (atGamma e.data g).original Q = ClaimTransport.batch g p
          and c1Projection p in EarlyC1Family.family e.c1.

    HighUnrecovered_F := HighPrefix and not RecoveredHigh_F.
    HigherResidual_F := higherPrefix and not RecoveredHigh_F.

Because `RecoveredHigh_F` includes the actual high witness,

    HigherResidual_F = HighUnrecovered_F disjoint-union LowPrefix.

This is the useful exact partition: multiply both indicators by the SAME
actual `suffix e g k t a A G`, then average over the original
Gamma/G/G/A domains. `SelectedHigherYProbability.pointwise_partition` and
its slice/probability counterparts give the existing ungated high/low
pattern. An analogous small gated adapter is still required here.

The cover's recovery conclusion concerns the SAME Q supplying the witness,
not an unrelated candidate. `witness_image` and the full fibre partition
turn its `HighSupport` premise into image validity and at least 200808
matching fibres. The cover applies to all such Q, without a literal-family,
ordinary-row, or higher-factor premise; the witness is needed only to
identify the actual event and final. A high witness outside the cover's
exceptions yields `RecoveredHigh_F`, contradicting `HighUnrecovered_F`.

This does NOT identify an arbitrary existing `residualProbability` or all
accepted prefixes with `HigherResidual_F`. Such an application must prove
its payoff is dominated by this event, or separately account for its
lower-degree, no-good, authentication and source-failure branches. It also
does not assert `earlyC1=some`, an efficient decoder, or payment extraction.

## Pair-first precedence and one suffix repair

Use the product `E = E_m * E_l`, fixed before both OOD draws. It is nonzero
and has degree at most

    D = 65061549 + 25345827 = 90407376.

Let `S = {t : QM31Exact | Admissible t and E.eval t = 0}` be its COMPLETE
admissible root set. The exceptional pair event is

    Pair_E := E(point(data,0))=0 and E(point(data,1))=0.

It is BOTH points, not either point. Each original same-obstruction pair
event is contained in `Pair_E`; different factors/obstructions may supply
the roots at the two points. The product event deliberately includes these
mixed pairs. Consequently it is a conservative superset, not equality to
the union of the two original pair events. Outside it, both original pair
events are false, which is exactly what the two component bounds need.

Use this precedence on successful terminal histories:

1. On `Pair_E`, bound the actual residual payoff by one using the unit
   bound for the SAME suffix. Do not separately apply a high or low repair.
2. Outside `Pair_E`, the new middle cover has one fixed pre-gamma set
   `bad_m` with cardinality at most `40+28+36=104`. Every
   `HighUnrecovered_F` prefix has gamma in that set. Bound its actual suffix
   by one; its total mass is at most `104/|Gamma|`.
3. The remaining actual LOW event is bounded by
   `SelectedRegularLowProbability.low_probability_bound`. This gives one
   common-row root charge `117049/|Gamma|`, the integrated query/alpha
   budget, and exactly ONE `q/|G|+18/|A|` suffix repair.

The middle set, the common-row roots, and the factor supports need not be
disjoint. Union/sum upper bounds suffice. In particular, do not replace
their sum by a maximum, multiply their marginal probabilities, or add a
fresh specialization/retention budget already included in the 40. If one
chooses root-first disjoint subevents, they remain bounded by the original
unconditioned component events; there is no renormalization by the
nonexceptional-domain size.

The existing LOW theorem already includes the 117049 root charge and
`integratedBudget`; neither may be added a second time. Its
`integratedBudget` already includes the conservative `3/|A|` cubic-alpha
charge. The separately written suffix term is only `q/|G|+18/|A|`.

## Exact theorem target and finite-history assumptions

Put `g=Gamma.card`, `a=A.card`, `s=G.card`, `N=P^4-P^2`, where
`P=2147483647`. Require nonempty Gamma/A/G, `g>=6752623450`, and
`0<q<=262144`. All averages are the original finite means. For each
successful OOD terminal history, an `Execution q` must have the SAME
pre-OOD C1/C2, checked data, circle equations, non-west chart conditions,
and first/second parameters equal to the actual decoded sampler values.
`SelectedMiddleGammaProbability.SourceAt` supplies the existing precise
shape of this source premise. Keep terminal history dependence: do not
collapse answers or executions to functions of the pair alone.

Write `R(e)` for the original gamma/kappa/tau/alpha mean of the actual
`HigherResidual_F` suffix. The proposed terminal estimate is

    R(e) <= 1[Pair_E] + C,
    C = 117153/g + integratedBudget(q,Gamma,A) + q/s + 18/a.

On pair-root histories, this follows from `R(e)<=1` and `C>=0`; elsewhere
it follows from steps 2 and 3. For an abort-preserving nested circle
experiment with the literal three-attempt distinct-second controller,

    pairPay(coins,draw,Admissible,between,R,h0)
      <= D*(D-1)/(N*(N-1)) + C.

The exact existing composition tools are
`NestedCircleContinuation.actual_exception_bound` (in
`NestedCircleContinuationV2.lean`) and
`RootSetPairMass.actual_one_call_target_bound`, followed by the polynomial
root-cardinality and monotonicity arguments used in
`MiddleSimplePairMassV4.pair_root_mass_numeric_le`.
The latter specialized numeric theorem itself is capped at 65061549;
do not call it as though it already proves the new 90407376 product bound.
The required new product-degree/card adapter is small but not checked by
this arithmetic script.

The sampler hypothesis remains exactly the history-uniform ordinary-draw
law

    NestedCircleMass.Generic.Uniform coins draw
      (ordinaryAtomMass
        (FiniteOptionMass.successMass OrdinaryPrefixMass.value)).

The finite coin set must be nonempty for the continuation bound. The
`between` function may absorb the first answer and alter all subsequent
histories. The law is required at each history, not inferred from two
independent-looking transcript labels. Aborts contribute zero; there is no
conditioning on successful samplers, no division by a retry success rate,
and no additional retry multiplier. Gamma is still the specified uniform
original-domain continuation, not an observed Fiat--Shamir distribution.
No ROM prequery/repeated-input/grinding coupling or source refinement is
supplied by this target.

## Exact layer cake and selected arithmetic

For `T=262144`, `q=22`, `L=9558`, `U=200807`, set

    B(m) = floor(251238108102656/(4*m-1026)),
    beta(m) = choose(m,22)/choose(262144,22),
    LC = beta(L)*B(L)
       + sum[m=L+1..U] (beta(m)-beta(m-1))*B(m),
    epsilon = min(1,3/a).

`SelectedRegularLayerCakeInstance.integratedBudget` is exactly

    (1-epsilon)*LC/g + 3/a.

The same-Q relation `4*m<=originalSupport.card+2` explains the denominator
`(4*m-2)-1024=4*m-1026`. The lower endpoint has denominator 37206 and
`B(9558)=6752623450`; the upper has denominator 802202 and
`B(200807)=313185591`. Both endpoints are included. The finite sum counts
factor occurrences with multiplicity; it is not a tail count for a union.

The script uses the Pascal identity
`choose(m,22)-choose(m-1,22)=choose(m-1,21)` and one common denominator.
It independently checks the result by summation by parts and checks tiny
off-by-one counterexamples. This is small integer arithmetic, not dense
finite-field elimination or a large generated Lean numeral.

For `k=P^4=21267647892944572736998860269687930881`, the recorded instance
uses `g=k-1`, `a=s=k`, and
`N=21267647892944572732387174255555510272`. These are explicit ideal-domain
choices, not a claim about the source's hash-output law.

| Term | Approximate mass |
| --- | ---: |
| Product pair, degree 90407376 | 1.807044305915173609e-59 |
| Middle gamma set, 104/g | 4.890056508529156062e-36 |
| LOW common roots, 117049/g | 5.503617541027203730e-33 |
| LOW integratedBudget, including 3/a | 4.379777686740350791e-32 |
| One suffix repair, 22/s+18/a | 1.880790964818906178e-36 |
| Total | 4.930816525590405970e-32 |

The exact total is retained as a reduced numerator/denominator in JSON;
all comparisons with `2^-103`, `2^-104`, and `2^-105` use integers/rationals.
Decimal values and negative logarithms are labeled approximations.
The script permits explicit alternate Gamma/A/G cardinalities and refuses
cardinalities violating the selected LOW theorem's hypotheses. They must
not be silently replaced by full-field cardinalities in a proof.

## Reproduction and scope

Run from the research worktree root:

    python3 docs/research/v8-no-work-100-20260907/experiments/residual_recovery_probability.py --check-recorded

Omit `--check-recorded` to print the full machine-readable record. Neither
mode writes files or invokes a compiler. The local calculation completed
successfully and both exact layer evaluations agreed. The arithmetic record
is final for this selected conditional ideal event. The product, exact
high/LOW partition, high-residual discharge, and selected non-pair adapter are
separately kernel-checked; see the composition, high-recovery, and selected
adapter reports. This does not turn the event into complete verifier
acceptance or a checked payment-witness extraction event.

Source inspection baseline: `7c8e18488f1337b1ff247908a1a8e86325ec29bb`.
The final focused source/evidence hashes and resource receipts are recorded in
the three theorem reports. Earlier source/evidence/report files and concurrent
sampler drafts were not changed.
