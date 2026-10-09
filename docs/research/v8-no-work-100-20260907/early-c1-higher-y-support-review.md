# Fixed-early-C1 higher-Y high-support count

Status: kernel checked. [EarlyC1HigherYSupport.lean](experiments/EarlyC1HigherYSupport.lean)
exports seven theorems audited with only `propext`, `Classical.choice` and
`Quot.sound`. The frozen source's initial draft comment predates this check;
the terminal v2 evidence below records the completed result.

## Exact result and causal order

`fixed_early_high_count` fixes C1, an actual `earlyC1 c1 = some p`, C2, and a
finite set Gamma of nonzero challenges. For any checked OOD data it bounds
`highHigherGammas.card` by **117077**. Membership means that some actual
natural-coordinate quotient Q simultaneously has:

- both image equations;
- at most `4*15334 = 61336` bad complete quotient fibres, equivalently at
  least `262144-61336 = 200808` complete matching fibres;
- a root equation for its reconstructed original's actual circle-GRS
  polynomial in some retained prime factor of Y-degree at least three.

Q and the factor are existential separately at each gamma. They can be the
same Q selected by a later alpha-dependent final; no final is fixed before
alpha. The count includes singular as well as regular roots. It requires
neither a derivative premise nor a supplied component tuple or candidate
family. It does not assert that every accepted execution has this support.

`fixed_early_dichotomy` exposes the construction rather than assuming it:
either fewer than three helper-good gammas exist, or one 29-message tuple
has C1 projection p and covers every such image-valid close Q. The tuple is
chosen from C1, p, C2 and Gamma **before all OOD data, gamma, claims and
strategies**. Gamma must therefore denote the fixed challenge domain, not a
postselected set depending on those later values. Its `Covers` predicate is
an output of the existing cover theorem, not an additional premise in the
final count.

## Reused source and V7 proof chain

| Ingredient | Exact reusable interface |
| --- | --- |
| Early object depends only on C1; threshold 245609 fibres | [EarlyC1Projection.earlyC1](experiments/EarlyC1Projection.lean) |
| Degree-two helper curve on the actual C1 own support | [ThreeHelperSelected.helper_degree](experiments/ThreeHelperSelected.lean) and `raw_near_helper` |
| Actual quotient-to-original map, including up to two pole fibres | [ThreeHelperClaimCover.close_original_on_support](experiments/ThreeHelperClaimCover.lean) |
| Constructed tuple or fewer than three good gammas | `ThreeHelperClaimCover.quotient_cover_dichotomy` |
| Sparse inclusion for every actual close image-valid Q | `ThreeHelperClaimCover.good_of_close_image` |
| Actual message-to-circle-GRS linear map | [SelectedGRSSubmodule.encoder_eq](experiments/SelectedGRSSubmodule.lean) |
| A fixed degree-28 curve has at most a factor's weight many roots | [HigherYCurveObstruction.coherent_specializations_card](experiments/HigherYCurveObstruction.lean) |
| Multiplicity-preserving sum of prime-factor weights | [FactorIdentityCover.all_factor_weights_le](experiments/FactorIdentityCover.lean), reusing V7 factor budgets |

The quotient-to-original support loss is already included: 61336 becomes
61338 on the C1 own support. The old helper-cover inequality is exactly
`4*61338+256 = 245608 < 245609`. No agreement outside that own support and
no global chord-nonpole assumption are introduced.

The new `tupleCurve_eval` identifies the degree-28 polynomial curve with
`exactCircleGRSPolynomial (ClaimTransport.batch gamma messages)`. The full
29 powers are retained. Helper degree two is used only for helper recovery;
the full component-claim error remains degree 28. This leaf does not charge
claim roots anew or prove a new claim-error bound.

`Generic.coherent_multiset_count` unions the challenge sets of all higher
prime factors. For each factor the fixed curve has at most
`trivariateYZWeight 28 F` specializations: a prime of Y-degree at least two
cannot have that polynomial curve as a global root. Multiset induction
preserves repeated factors and uses union subadditivity, not disjointness.
The summed weights are at most the parent's weight, which is below 117078.
Thus the dense branch costs 117077 total, **not 111 times that number**.
In the sparse branch the same actual Q-to-good-gamma inclusion gives at
most two challenges, already below the advertised coarse bound.

## What cannot be inferred from this result

The premise that earlyC1 is populated remains essential at this threshold.
The older [NearGammaSelectedCoefficients.raw_message_cover_dichotomy](experiments/NearGammaSelectedCoefficients.lean)
can derive a populated early object from at least 64 near gammas with at
most 9301 bad original fibres. The direct quotient transfer makes at least
252845 complete quotient matches sufficient for that stronger closeness.
This is not a proof that 200808 matches populate earlyC1, nor a removal of
the `earlyC1 = none` branch.

A small exact algebraic countermodel rules out the tempting one-gamma
shortcut. Over F7 take a constant code on the five coordinates
X in {2,3,4,5,6}, with early threshold four coordinates. Set C1 lane zero
to X, lane one to -X, and all other C1/helper lanes to zero. Every constant
matches lane zero at most once, so no early tuple has four-coordinate
support. The raw gamma word is `(1-Z)X`; helpers have degree zero, within
the degree-two constraint, and all gamma degrees are within 28.

Let `H=X(X-1)` and `F=Y^3+Y-(Z-1)H`. At OOD coordinates zero and one,
both fixed answer polynomials are zero and both derivative curves equal
one. F is primitive linear in Z over F7[X,Y]: its coefficients `-H` and
`Y^3+Y+H` are coprime. It is therefore irreducible, hence prime. At gamma
one, U=0 is a polynomial root and matches all five raw coordinates.
Consequently even a fully matching **regular** higher-Y root at one gamma
does not imply a populated early object. This is a mathematical toy, not
an instance of the selected QM31 encoder, interpolant choice, acceptance
predicate, sampler or payment relation.

No gamma/query marginal multiplication is justified here. An eventual
consumer must retain the actual joint event, including low-support and
early-none remainders. Authentication/access, actual transcript freshness,
efficient extraction and payment validity remain separate obligations.

## Focused verification and retained failures

Research source parent: `96046bac27e443a67cd4a3820d1c0801f94816fa`.
Inherited cache pin: `289d7356c78a4cd493fe61a54f9548f2a0c11298`;
borrowed V7 source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The parent agent ran both serial NUC checks over Tailscale; this agent
inspected the copied evidence and hashes locally.

| Attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Result |
| --- | --- | --- | --- | --- | --- |
| [v1](experiments/early-c1-higher-y-support-nuc-v1.log) | 1 | 4.85 s | 6832320 | 0 | Three generic audits passed; selected namespace/alias errors and resulting failed elaboration. Not a green module. |
| [v2](experiments/early-c1-higher-y-support-nuc-v2.log) | 0 | 3.82 s | 6877452 | 0 | All seven audits standard-only; preflight/postflight both passed 951 entries unchanged. |

The repair removed an ambiguous open namespace, named the selected QM31
alias, opened the actual `SelectedFactorCoherence.parent` namespace, and
used a target-directed parent-weight bound. No memory, heartbeat or
recursion limit was increased, and no field/domain enumeration was added.
Both exact source snapshots and per-run manifests are retained next to the
logs. V1's selected `sorryAx` diagnostics are failure evidence, never
theorem credit.

The focused runner was
`run_higher_y_nuc.sh TASK EarlyC1HigherYSupport early-c1-higher-y-support-nuc-v2`,
with TASK `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`.
Lean 4.32.0 used `-j1 -M9500`; cgroup MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0 and CPUQuota 200%. Module limits remained depth 200 and
250000 heartbeats. No package replay or cold dependency build occurred.

| Green artifact | SHA-256 |
| --- | --- |
| Source / exact v2 snapshot | `621ad297e6b7248cc40f6da0060db205e01f0977fb97c46882794f01f055f64a` |
| Olean | `b6d6de6883a3ca7ad71e4e0c00736335acddb04649b966e73966f35b4c9450d3` |
| V2 manifest | `4b93c734de4ffcbe03b01df2af47666bcccaccdd6be1b9d9768bdb26625c9ac4` |
| V2 log | `4e16b0e265e687e3b1e31860429b4828f36e800a5f0a220c8a9dcf8a92e8da7b` |
| Runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
