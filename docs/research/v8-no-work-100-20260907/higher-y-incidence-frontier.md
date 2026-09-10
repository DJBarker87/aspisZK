# Higher-Y frontier and a direct-incidence specialization tail

Inspected source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: source review and mathematical derivation, with the four-theorem
`experiments/HigherYCurveObstruction.lean` core **kernel-checked on NUC v2**.
No old Lean target, certificate, or runtime fixture was replayed.

## Current frontier, not the older checkpoint's next-step text

| Factor/class | Committed endpoint | Exact remaining boundary |
| --- | --- | --- |
| Y-degree zero, excluded positive factors | `FactorIdentityCover.exists_identity_factor_cover`, selected `SelectedIdentityCover`, `CausalFactorReduction` | Covered by the existing 117077 gamma exception in the ideal suffix, once; authentication and source laws are separate |
| Y-degree one | `SelectedLinearCover.exists_selected_classification` | Pre-OOD linear obstruction degree26854534485; sparse gamma set3108; otherwise an actual29-message tuple in a fixed family of size111 |
| Represented tuple | `SelectedOwnSupportGame.literal_family_count`; `SelectedOwnSymbol.own_supported_early_member` | Insufficient own support has a joint gamma/alpha/query bound; sufficient own support gives early-C1 family membership, not a checked witness |
| Y-degree two | `SelectedQuadraticCover.fixed_cover`; `SelectedQuadraticReduction`; `CausalQuadraticReduction.exists_total_reduction` | Fixed E degree114687 and fixed bad-gamma set936616; OOD indicator and downstream source/extraction obligations remain |
| Y-degree3 through111 | `SelectedQuadraticReduction.HigherCubicRoot` | Same actual reconstructed candidate is a root of one retained prime factor; no current general cardinality/coverage bound |
| All remaining accepted factor mass | `CausalQuadraticReduction.residualProbability` | Literally factorPrefix AND NOT quadraticPrefix; it also includes linear/tuple/recovery branches and is not just HigherCubicRoot |

The bound111 is `SelectedLinearCover.parent_y_degree`. Additivity of prime
factor Y-degrees gives at most37 factors of degree at least3, counting
multiplicity, hence also at most37 distinct such factors. The ambient positive
factor universe has at most111; multiplying a worst-case higher-factor tail
by111 would throw away the available additive budget.

The historical `higher-y-continuation.md`, `higher-y-obligations.json`, and
`quadratic-recovery-ledger.json` deliberately describe earlier checkpoints.
Their then-pending Sylvester, parity, source-map and quadratic-family steps
were subsequently discharged. Current quadratic algebra is in
`quadratic-selected-cover-review.md` and the accepted-mass interface is in
`quadratic-causal-review.md` / `quadratic-causal-ledger.json`. No historical
proposed numerator is a fresh charge.

## Strongest next theorem: actual regular higher-factor incidence tail

Fix arbitrary received C1/C2, their actual chosen parent P, and the actual
OOD data d. Write

    N = 1048576, D = 1024, c = 28,
    W_F = trivariateYZWeight 28 F,
    B_F = 28 + 2047 * (W_F - 28).

For each fixed prime factor F of P with Y-degree at least3 and both actual
OOD polynomial identities, choose ONE of the actual OOD points t and its
actual answer polynomial A(Z), before gamma. The new checked
`MonicOODBranch` interface constructs the literal local branch directly.
For the regular-event theorem below, no full separability-certificate or
normalized-local-factor-membership premise is needed. The nonempty regular
event itself witnesses that the actual derivative curve is nonzero. This
does not prove that every retained factor has a regular actual OOD branch.

For `1024 < M <= N`, define S_F(M) to consist of gamma values in a supplied
fixed finite Gamma for which there EXISTS a quotient Q satisfying:

1. Q belongs to the literal received-quotient family at that gamma and is
   image-valid, with the existing Checked/circle/nonwest data guards.
2. Its actual original message `U = exactCircleGRSPolynomial
   ((atGamma d gamma).original Q)` has at least M original-symbol matches
   against the normalized received29 batch.
3. `challengeCandidateHom gamma U F = 0` for THIS F.
4. The actual derivative `(partial_Y F)(t,A(gamma),gamma)` is nonzero.

The proposed conclusion is the integer inequality

    (M - 1024) * card(S_F(M)) <= N * B_F.                 (1)

This existential set covers arbitrary post-alpha Q choices. A choice of one
qualifying Q per gamma is only a proof device for the contradiction; it
does not move an actual final before alpha, change the fixed family, or
assume that the chosen candidates already lie on a component curve.
Literal family membership supplies M=38230 automatically through
`CoveredOriginalSymbols.family_member_original_38230`. Larger M uses the
candidate's actual matching set, not disclosed sample counts.

### Exact dependency chain

1. `CoveredOriginalSymbols.selected_width29_valid` derives the old V7
   valid-response interface from the literal Q/image hypotheses. It preserves
   arbitrary received words and loses only two symbols at the chord poles.
2. Use the literal monic local branch `Y-A(Z)` directly. The checked
   `MonicOODBranch` gives degree1, leading coefficient1, irreducibility over
   the rational field, and an empty local pole set. A degree28 answer yields
   coefficient weight bound28 (the exact weight can be smaller). The same
   actual point equality for U comes from
   `SelectedIdentityCover.literal_candidate`, not a supplied equality.
3. A single regular gamma makes the derivative curve a nonzero polynomial.
   `MonicOODBranch.exists_source_hensel_root` constructs the borrowed V7
   power-series root from this and the retained identity;
   `MonicOODBranch.derivative_nonzero` constructs its nonzero regularized
   denominator. These reuse `PowerSeriesLift` and `RegularHensel`; no
   normalized local-factor membership or full resultant is required.
4. `V7ExactCorrelatedAgreementFixedBranchCurve.
   exists_ambient_curve_of_fixed_branch` takes the ACTUAL support incidences.
   Its threshold is `1024*n + N*B_F < n*M`. It permits arbitrary gamma-indexed
   candidates. With local degree1/weight28, the existing
   `fixedBranchEvaluationBudget` simplifies exactly to B_F above.
5. `V7ExactCorrelatedAgreementReleasedLift.
   exists_exactInitial_components_of_ambient_curve` needs only `28<n` and
   returns29 actual source messages containing EVERY selected candidate.
   Do not reintroduce the convenient outer-wrapper overhead `28*N+1`.
6. Form their fixed polynomial-in-Z original-GRS curve V(X,Z), degreeZ<=28.
   All selected gamma values make F(X,V(X,gamma),gamma) identically zero in X.
   Its Z-degree is at most W_F. If n>W_F, root counting over the integral
   domain K[X] forces F(X,V(X,Z),Z)=0. A prime F with Y-degree>=2 cannot have
   such a root: `Y-V` divides F and forces its Y-degree to be1.

Step6 is the new four-audit checked `HigherYCurveObstruction.lean`. The
nonexistence of an irreducible higher-degree polynomial root itself is
already Mathlib's `Irreducible.not_isRoot_of_natDegree_ne_one`; the new
adapter transports the challenge specialization and weighted degree/root
count. It does not supply the V7 incidence premises.

To prove (1), argue by contradiction. Since W_F>=28 and
B_F>=W_F>=28, the failed inequality implies n>B_F (because M-1024<=N),
therefore n>W_F and n>28. Thus every cardinality prerequisite of steps4-6
follows from that single failed incidence inequality. No assumed candidate
curve, extra large-subset premise or provider coverage is needed.

## Additive union and exact arithmetic

The fixed retained higher factors share
`sum W_F <= 117077`, by `FactorIdentityCover.all_factor_weights_le` and the
selected parent bound. For a nonempty family of k such factors,

    sum B_F = 2047 * sum W_F - 57288*k
            <= 2047*117077 - 57288 = 239599331.

The empty case contributes zero. Unioning their qualifying gamma sets in
(1), without any disjointness assumption, gives the proposed tail

    (M-1024) * card(union_F S_F(M)) <= 251238108102656.

At M=38230, the integer cap is **6752623450**, not111 times that number.
Under uniform nonzero gamma only, its ratio to
`(2147483647^4)-1` displays **91.34719903331277 bits**. This arithmetic was
computed exactly with integer division before the decimal logarithm. It is
a conditional regular-branch bound, NOT a checked new probability theorem
or a100-bit result. The older convenient fixed-branch threshold is
6977740728; the direct-incidence interface avoids that extra slack.

### Singular branches: separate proposed prerequisite

For each fixed prime higher factor, the existing nonzero resultant
`separabilityCertificate F` gives a nonzero X-coefficient obstruction E_F
whose nonvanishing at an actual OOD point certifies that the specialized
resultant is not identically zero in Z. Product these E_F before OOD. If
both OOD points are not roots of the product, each F has an actual point
with a usable certificate; different F may choose different rows.

At that point the retained polynomial identity forces the actual derivative
curve to be nonzero. Its gamma degree is at most W_F-28, not the coarser
resultant degree `(2*degreeY(F)-1)*degreeZ(F)`. Summing these root exceptions
would cost at most117049 for a nonempty retained higher family. The proposed
regular-plus-singular numerator is then6752740499, displaying
91.34717402606195 bits. This derivative cover and its source adapters are
NOT in the new draft.

A conservative X-degree for the pre-OOD product is
`221*114687 = 25345827`, using degreeY<=111, degree of its nonzero derivative
at most110, and the additive factor X-degree budget. Both the source-point
certificate transport and the numerical221 sharpening need proof before
that value becomes a certificate. Do not replace actual OOD points by the
unrelated existential smooth point selected by old V7 OuterSelection.

## False shortcuts and exact causal constraints

- Parent squarefreeness is not available: honest-compatible `(Y-U)^3` can
  have an identically zero derivative along the whole answer curve. Work on
  actual prime factors with explicit specialization guards.
- `RationalHelperIdentity` and `RationalHelperSpecialization` refute
  two-identities-plus-regularity => global polynomial component curve.
  Their fixed-C1zero example has helpers `(-b/(X-a),1/(X-a),0)` and the
  degree27 raw numerator `Z^26*(Z-b)`; its sole nonzero good gamma is b.
  The new many-specializations contradiction is consistent with this.
- `LinearDenominatorRegression` proves that resultant alone misses degree
  drop: `(XZ+1)Y+1` has a polynomial answer at X=0 although its resultant is1.
- The newly discussed cubic control
  `(Y-A(Z))^3-(Z-1)H(X)^3`, with H vanishing at the two OOD points, has many
  horizontal roots but singular OOD sections. Against raw=A the alternative
  roots have only H-root agreement. This is a root-only obstruction, not a
  support-qualified or authenticated payment counterexample.
- Simple-root rigidity proves uniqueness only at a fixed gamma/branch;
  it does not supply a polynomial curve across gamma or guarantee existence.
- Keep exact C1 fixed before lambda/chi; adaptive C2 and P depend on the
  later prefix, so this family is pre-OOD, not pre-lambda. The map works for
  arbitrary C1/C2 without pretending an early decoder succeeded.
- `FixedC1FarMoment.helper_degree` is degree2 at every stored helper symbol.
  `raw_on_own_support` permits known-C1 subtraction only on established C1
  support. The joined wrong component-claim polynomial remains degree28.
  This width29 branch theorem therefore uses c=28, not c=2 globally.
- The actual final remains post-alpha and pre-query. A finite existential
  gamma set containing every such qualifying candidate is safe; supplying
  a postselected fixed message family or multiplying a bare query tail is not.

## Stopping point

The direct theorem (1) is now kernel-checked as
`HigherYRegularBranch.regular_branch_count`; its source-shaped derivation and
13-audit NUC evidence are recorded in `higher-y-regular-branch-review.md`.
`SelectedHigherYBranch.lean` is a separate four-audit **checked
source bridge**: its `higher_prefix_branch` produces membership in the
fixed factor family, the retained identities, actual final representation
by the same Q, derived `Width29ValidResponse`, and both actual OOD values.
Its maximal `qualifyingGammas` existentially covers every later Q choice;
`qualifying_regular_or_singular` retains derivative-zero separately. The
prefix is restricted to `HigherCubicRoot` for that SAME Q, not all residual
mass and not arbitrary accepting proofs. The remaining adapter must connect
that selected event to the checked direct theorem without losing its causal
support and regular-row premises.

The exact layer-cake consumer in `higher-y-regular-tail-review.md` shows the
standalone regular support/query tail is only 96.09536 bits when all support
sizes remain residual. It reaches100 bits only if checked extraction covers
support above230445 fibres, and reaches105 bits only with coverage above
195385. This makes high-support payment extraction, rather than another
unstratified incidence lemma, the decisive regular-branch obligation.
No sampler/FS, authentication, own-supported tuple-to-payment extraction,
resource-bounded replay, or full-view privacy gate is closed by this map.

## Focused core evidence

Only the new leaf was compiled, using inherited runner/cache parent
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, source-work parent `e969d9fa`, and
borrowed V7 pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The source's initial “Draft, not checked” comment is retained as the exact
preflight source text; this section and the successful log record its later
check without editing a green source.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Status |
| --- | ---: | ---: | ---: | ---: | --- |
| `higher-y-curve-obstruction-nuc-v1` | 1 | 2.86 | 6798900 | 0 | ASCII `!=` selected Boolean equality; bounded `forall ... in` parser syntax |
| `higher-y-curve-obstruction-nuc-v2` | 0 | 3.02 | 6831824 | 0 | Four standard-only axiom audits; both 889-entry provenance checks pass |

The v2 repair changes only those two symbols, with no resource-limit change.
All attempt source/log/manifest snapshots and the green output are retained
under `experiments/`. No `sorry`, added axiom, or native decision procedure.

- Green source: `37625775cbebc5aedf63d3ccf99cce36724d0ac8df68701698175db126a4bf82`.
- Green output: `6371d6cf82707ae408f74157a3911116c7e93556c0fba77c426771cdfba73c33`.
- Green manifest: `8a07dfd27519ffe480caf3742080656458799c7ffbd861799136fa3e3c7bacdf`.
- Runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The actual endpoint was Tailscale `dombarker@100.108.41.90`, with
`HostKeyAlias=nuc.local` used only for the pinned host key. Command:

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  HigherYCurveObstruction higher-y-curve-obstruction-nuc-v2
```

Logged caps: MemoryHigh=8589934592, MemoryMax=10737418240,
MemorySwapMax=0, CPU quota=200%; Lean 4.32.0, `-j1 -M9500`.
The native package cache remains a declared pinned compiler-cache boundary,
not a new replay of Mathlib or the V7 dependency suite.
