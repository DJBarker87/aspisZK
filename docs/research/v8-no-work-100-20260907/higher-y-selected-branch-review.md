# Actual selected higher-Y branch: source bridge

Source-work parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: `SelectedHigherYBranch.lean` is kernel-checked on NUC v2, with four
standard-only axiom audits. The separate `HigherYCurveObstruction` core is
also checked. Only these focused changed leaves were compiled; no new
borrowed cache or package build was needed.

## Literal event and timing

`Qualified c1 c2 d F gamma Q` contains three facts about the SAME Q:

- membership in `literalFamily (SelectedComponentGame.received c1 c2 d gamma)`;
- the actual quotient image equations;
- annihilation of F by the GRS polynomial of `(atGamma d gamma).original Q`.

`qualifyingGammas` filters a supplied fixed finite Gamma by existence of
such a Q. Thus it contains all possible later Q choices. It does not select
one candidate before alpha. `higherPrefix e gamma kappa tau alpha` also
requires that this SAME Q represents the actual final at tau/alpha, is not
a bad anchor, and satisfies the existing literal `HigherCubicRoot` predicate.

The factor multiset `curvePrimeFactors (parent c1 c2)` is fixed before both
OOD points and their answers. C1 is fixed even earlier, before lambda/chi;
C2 and therefore this parent may depend on that earlier interaction.
The `Retained` restriction and an actual OOD row r are fixed after the
completed OOD interaction but before gamma. A general accepted or residual
prefix is not silently identified with `higherPrefix`: the latter is a
restricted same-candidate class and may overlap other algebraic classes.

`higher_prefix_branch` derives image validity from `notBad`, invokes the
existing support bridge, and preserves the actual final equality. It makes
no decoder-success or received-polynomiality assumption. The support is the
complete actual original-symbol matching set, not sampled disclosures.
The literal 9558 complete fibres supply 38232 symbols; at most two chord
pole symbols are removed, giving strictly more than 38229 matches.

## Exact input map for the regular-branch theorem

Fix F and one row r, and put `S = regularGammas c1 c2 d F r Gamma`.
For each gamma in S choose one witnessing Q(gamma), extending Q arbitrarily
outside S. This is a mathematical choice in a cardinality proof. Since S
already existentially covers every actual later Q, choosing a witness here
does not restrict the actual post-alpha strategy.

Let `s = CoveredOriginalSymbols.originalStrategy c1 c2 d Q`. The new
`qualified_valid` deliberately takes this whole gamma-indexed Q function,
so no constant-strategy equality transport is needed.

| V7 `exists_ambient_curve_of_fixed_branch` input | Actual source construction / proof |
| --- | --- |
| Domain and points | `Fin 1048576`, `exactInitialGRSConversion.points`, its existing injectivity theorem |
| Candidate(gamma) | `exactInitialGRSConversion.messagePolynomial (s.candidate gamma)`, definitionally the actual reconstructed original-Q GRS polynomial |
| Support(gamma) | `s.support gamma`, the literal `symbolSupport` from `originalStrategy` |
| Support cardinality | `(qualified_valid ... gamma qualified).1`, so `38229 < card` |
| Received coordinate curve | `receivedCurvePolynomial (exactInitialNormalizedLanes (received29 c1 c2)) i` |
| Candidate/support agreement | `(qualified_valid ...).2`, followed by exact nonzero column-multiplier normalization described below |
| Candidate degree and received degree | `exactInitialGRSConversion.messagePolynomial_degree_le` gives 1024; `receivedCurvePolynomial_natDegree_le` gives 28 |
| Same-factor root | `Qualified`'s third field, not a root of some other factor or candidate |
| Local root | `qualified_points` at r, then `MonicOODBranch.branch_local_root` |
| Simple specialized root | The same-factor root evaluated at the actual OOD point, plus the nonzero actual derivative in membership of `regularGammas` |
| Pole-free local branch | `MonicOODBranch.branch_poles`: the literal monic `Y-answerCurve` has no leading-coefficient poles |
| Formal root / eta | Retained row identity plus `MonicOODBranch.exists_source_hensel_root` and `derivative_nonzero`; nonempty S supplies one nonzero derivative evaluation, hence a nonzero derivative polynomial |

The normalized agreement step is important. Write m(i) for the existing
nonzero `exactInitialGRSConversion.multipliers i`. The old valid response is
an equality of released circle-code symbols, not directly a GRS evaluation:

    candidate(gamma)(points i)
      = m(i)^(-1) * exactInitialEncoder (s.candidate gamma) i
      = m(i)^(-1) * width29CurveValue (received29 c1 c2) gamma i
      = received(i)(gamma).

Its exact existing bodies are in the initial-code section of
`V7ExactCorrelatedAgreementConcreteBranch`: `exactInitialEncoder_coordinate_grs`,
`exactInitialGRSConversion.multipliers_ne_zero`, and
`exactInitialNormalizedLanes_curve`. No initial circle code is identified
with the entire ambient degree-at-most-1024 polynomial space. The old broad
concrete wrapper need not be replayed: only this pointwise normalization is
needed before the generic fixed-branch incidence theorem.

For the simple-root predicate, `Qualified`'s candidate root and
`specializeEvaluationPointChallenge_eval_candidate` give its root half.
`FactorCoherence.pointSubstitution_eval` and
`specializeEvaluationPointChallenge_derivative`, with the actual point
value from `qualified_points`, identify its derivative half with precisely
the nonzero scalar used by `regularGammas`. No resultant or all-branch
smoothness premise is substituted for that actual scalar.

## Still open after this source adapter

The selected leaf does not invoke the incidence theorem or prove its
threshold. The forthcoming regular-branch consumer must still instantiate
that theorem with the monic coefficient budget, recover the fixed curve,
and apply the checked `HigherYCurveObstruction` specialization count.

If the recovered ambient curve is passed through V7's released-message
lift, first multiply each normalized ambient coordinate by `C (m(i))`.
`exists_exactInitial_components_of_ambient_curve` needs only `28 < card S`.
Its actual 29 messages then define a fixed degree-at-most-28 polynomial
curve of original GRS polynomials using `SelectedGRSSubmodule.encoder`'s
linearity. This is where coherent component curves are derived; none is
assumed by `Qualified` or the causal prefix.

`qualifying_regular_or_singular` retains the alternative derivative-zero
scalar exactly. It assigns no small probability or finite root count when
the derivative curve is identically zero. The standalone proposed regular
tail, its additive factor union, the singular-branch cover, and the joint
query/acceptance composition remain separate obligations. The helper curve
is degree2 only on its established source support; the width29 claim-error
curve used here remains degree28. No final is moved before alpha, and no
bare query tail receives a gratuitous factor-family multiplier.

## Focused evidence

Only pinned `SelectedQuadraticReduction` and `CausalFactorReduction` are
direct imports. The successful command was:

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SelectedHigherYBranch selected-higher-y-branch-nuc-v2
```

Transport is Tailscale `dombarker@100.108.41.90` with pinned key alias only.
Runner parent remains 289d7356, distinct from source parent e969d9fa;
borrowed V7 remains 26a9cd47. Same established 8/10 GiB memory, swap0,
200% CPU and `-j1 -M9500` limits. Every attempted source/log/import snapshot
and the green output are retained under `experiments/`.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| `selected-higher-y-branch-nuc-v1` | 1 | 2.93 | 6829624 | 0 | Missing namespace open for exactInitialEncoder and reserved `prefix` binder |
| `selected-higher-y-branch-nuc-v2` | 0 | 3.34 | 6868288 | 0 | Four standard-only audits, no warnings, both 897-entry provenance checks pass |

The source repair adds one namespace open and renames the binder; no
statement, model or limit changes. The v1 diagnostic `sorryAx` was produced
by the failed elaboration and is not a retained proof. V2 has only
`propext`, `Classical.choice`, and `Quot.sound` in each audited closure.

- Green source: `a933e50a7cde61e00d8c68770d9200cea8656c9d3736edb26fc781ee4c998084`.
- Green output: `cca91bde733766bffe794feea7f8aa46062c91c394107fdeded4ce1791d34762`.
- Green manifest: `7886d5866546c1192d61d2ac252bc96f9fdd0473f384a398eb2bf4c146eff9f5`.
- Runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

At preflight the host had 43 GiB available. An unrelated V7 assembly scope
was active and was preserved: its MemoryMax was 10 GiB and swap limit zero,
so the combined reserved maximum with this scope was 20 GiB. This result
does not claim an otherwise idle host. Native package artifacts remain the
declared pinned compiler-cache boundary, not a fresh Mathlib replay.
