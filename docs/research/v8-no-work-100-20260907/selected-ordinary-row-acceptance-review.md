# Selected ordinary-row acceptance boundary

Status: focused NUC replay passed.
Source parent: `eb06c838bdeb002508dac2b4af406631f3d67e66`.
Owned target: [SelectedOrdinaryRowAcceptance.lean](experiments/SelectedOrdinaryRowAcceptance.lean).
Retained source SHA256: `ba37ffc3bd10ea8ff9f1d3c082e7059cfc5043a40abbf68cd5275037f16518e5`.
Seven axiom audits all report only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` remains.

## Result and exact limitation

The ordinary-row premise of `SelectedMiddleComponentClaimsV2.family_claims_exact`
already follows from the SAME quotient's `not badAnchor` gate. It does not
require an additional sampled-kappa repair on the recovered-good branch.
`SelectedResidualHighRecovery.RecoveredHigh` retains this gate inside its
`Witness`, together with the representation by a member of the fixed component
family. The new `recovered_high_claims_exact` composes these existing facts,
outside the family's fixed component-claim exceptional set of cardinality at
most 28. Neither this family nor its exceptional set depends on the sampled
gamma, kappa, tau, alpha, queries, rho, or final selected quotient.

Terminal acceptance alone does **not** imply that all four ordinary-row errors
are zero. An accepted no-good event remains in the exact partition; it is not
silently promoted to a good quotient. This leaf supplies a typed boundary,
not `verify_parsed success -> Execution` or complete global soundness.

## New interfaces and reused proofs

| New declaration | Exact role and reuse |
| --- | --- |
| `callback_accepts_iff` | Builds the strategy with `withFields` and reuses `TypedRelationTerminalV3.source_accepts_iff` for the same decoded response0/final/query order/rho/later fields. No equality to an unrelated strategy is assumed. |
| `good_rows_zero` | Extracts the third `badAnchor` disjunct's negation and transports it with `GammaComponentGame.reference_rows` to the literal `ComponentRows.rows` construction. |
| `callback_partition` | Splits the actual typed scalar acceptance event into accepted no-good and accepted good-representative branches; derives row zero for that same good representative. |
| `good_represented_claims` | Calls `SelectedMiddleComponentClaims.family_claims_exact` with the derived row-zero proof and the same Q/p representation. |
| `recovered_high_claims_exact` | Consumes the existing `RecoveredHigh` payload. The returned Q retains its Witness, HighSupport, same-p representation, and all 87 exact component claims. |
| `fixed_claim_exception_card` | Reuses the single fixed-family union bound of 28; not three row charges or 87 cell charges. |
| `repair_once` | Retains `CausalCoveredRecovery.probability_partition` and `missing_bound` with precisely the existing no-good ceiling. |

The prior `NestedMiddleClaimExtraction.recovered_original_row_match` proves
the same row-zero transport for nested four-alpha/29-gamma reconstruction.
It is evidence for reuse, not imported or recompiled here: the new consumer
instead uses the fixed-family residual recovery and its 28-root exception.

The accepted terminal identity also composes directly with the existing
`CausalOrderedRelation.acceptance_iff_terminal_zero`, using `e.quarterChecked`.
That gives terminal zero for the SAME typed suffix; it supplies no extra
ordinary-row equality.

## Corrected source order and row equation

The inspected research source is pinned at the parent above. The three files
previously compared with positive/devnet checkpoint
`9e432896a4e1515efebe940b71fd9b4f9f009189` still have those same hashes.
This is a source inspection, not a new executed-binary receipt.

| File | SHA256 |
| --- | --- |
| `experiments/performance_verifier.rs` | `bf8a24c42c0d5493d2259fa19a70b1a8bf4ba168f661b71cfed6d33c70eebfbc` |
| `experiments/inactive_row_binding.rs` | `4642f1e4361aeb9f991ef917f8efdea292187fe3de9e3a9d351230859f9ad98b` |
| `experiments/structured_weights.rs` | `06befd20c084234ce1afa2d7cf3612a12370fdb0e98e95db30d89cf245b51089` |
| `experiments/relation_callback.rs` | `285c90695cc7558a88ffc7cb50de4235b68c7ceed9d0600d5cc9ba7f682607ed` |

Actual order, not the old V7 Tag73 schedule:

1. `performance_verifier::semantic`, lines 33–69: C1, lambda/chi, C2,
   theta/z/mu, eta, ten compact semantic response/challenge rounds, then the
   semantic terminal comparison using point claims. Claims are absorbed in
   the next preparation stage; a host comparison does not itself absorb bytes.
2. `inactive_row_binding::to_gamma`, lines 56–63: absorb all 87 point claims
   `v[271..358]`; draw first OOD point; absorb answer vector `v[359..388]`
   with row byte 0; draw up to three second-point candidates until distinct;
   absorb `v[388..417]` with row byte 1; absorb gamma nonce; draw nonzero gamma.
3. `structured_weights::prepare`, lines 122–173 (dense counterpart in
   `inactive_row_binding::prepare`, lines 129–153): absorb inactive scalar
   `v[358]`, then sample nonzero kappa. The three point-row scales are
   `[kappa, kappa^2, kappa^3]`; the inactive mask keeps coefficient one.
4. Construct the chord `(a,b,c)` and affine OOD interpolant; reject a zero
   interpolation denominator. Subtract its constant/selected-axis contribution
   from the batched claim. The axis coefficient is index 2 for x and 1 for y.
   The ordinary covector is the chord-reconstruction transpose, not a query
   covector. `ComponentRows.source_claim` and `OODInterpolantRows` provide the
   corresponding algebra, conditional on matching the source's weights/data.
5. The structured v2 transcript binds its literal descriptor, including
   `[20,22,10,4,4,use_x]`, semantic point, shifted scales, chord/interpolant,
   both OOD points, gamma, and all 64 expanded binary row masks. It then binds
   the corrected claim and the compact-functional image-gate tag before tau.
   The dense path has different profile bytes; differential arithmetic does
   not equate these transcript framings.
6. `structured_weights::relation`, lines 176–225: response0 at `v[417..423]`,
   fold nonce, alpha0, final256 at `v[441..697]`, ordered queries, then rho.
   Opening/authentication succeeds before query injection. The fresh query
   covectors live in dimension 256 and do not pass through chord transpose or
   alpha0. The three later compact responses precede their respective alphas.
   Final acceptance compares the ordinary-plus-query dot product, plus the
   deferred image terminal times final coordinate 3, against the carried claim.

For a fixed quotient Q, let `epsilon_j` be `ComponentRows.rows.errors j`.
The corrected initial discrepancy is exactly

`epsilon_0 + kappa*epsilon_1 + kappa^2*epsilon_2 + kappa^3*epsilon_3`.

This is `ShiftedRowPrefix.before_prior_cubic`, not a claim that one zero
evaluation implies four zero coefficients. The inactive claim may depend on
gamma but precedes kappa; the three component-claim arrays and functionals
precede gamma. The arbitrary helper contribution has degree two, while the
29-component claim-error polynomial still has degree at most 28.

## Falsification and repair accounting

The elementary counterexample to one-evaluation row binding remains even
after the correct shift: for nonzero a take errors `[-a,a,0,0]` and kappa=1.
The aggregate vanishes although the row vector is nonzero. This describes the
local algebra only, not a claimed selected-source successful forgery. The
existing Rust unshifted regression makes the same cancellation structural in
the unshifted path; its shifted controls do not prove rejection for every
challenge. Their corrected residual is `(kappa-1)*gamma^27*forged`.

The existing no-good bound is

`outsideQueryCeiling + 99*(3/|G| + 6/|A|) + q/|G| + 18/|A|`.

The 99 multiplies early bad-anchor collisions only. The q/G query-batch and
18/A later-round repairs appear once in that bound. There is no extra 3/G
cost in `good_rows_zero` or `recovered_high_claims_exact`.

For a global no-good-plus-low/residual bound, do **not** simply add complete
suffix bounds and then assert the repair was charged once. The union-moment
integration remains a separate obligation; no product of marginal
probabilities or independence assumption is supplied by this leaf.

The new fixed claim-error set of size at most 28 is separate from the
previous recovery bad set of size at most 104. It can be unioned if needed;
no disjointness or automatic absorption into the old 104 is asserted. A
28/|Gamma| probability charge additionally needs the appropriate uniform
gamma experiment; the new declaration is a cardinality statement only.

## Remaining source correspondence

The still-missing source constructor must simultaneously establish:

- Canonical successful parsing and exact decoded compact buffers/response
  history, not the zero defaults of an arbitrary malformed buffer.
- Fixed total C1/C2 words and agreement of all opened values with those words,
  or the supplied collision alternative. A post-query `observedWord` is not
  commitment binding. The new callback uses `oracle 0 (e.raw gamma)` explicitly.
- The actual selected three MLE functionals and inactive masks equal
  `e.weights`; all 87 claims and OOD answers equal `e.claims` and `e.data`;
  source chord, affine subtraction, and optimized structured terminal agree
  with the typed maps. Existing algebraic bridges can be reused but this leaf
  does not translate Rust or verify every optimization flag.
- The single fixed prefix and causal Fields work across all continuations,
  preserving the actual structured framing and adaptive final. One successful
  run does not construct that history-uniform family automatically.
- The actual sampler/tape or ROM law, repeated/prequeried-input handling,
  retry/abort accounting, and any FS loss. None follows from typed acceptance.

Malformed/source/authentication failures remain outside the successful typed
event; lower-degree, low-support, and other good-but-not-recovered branches
are not discharged by this row-to-claims bridge.

## Verification evidence

Direct imports and inspected local source hashes:

- `TypedRelationTerminalV3`: `05a8ea8a361cbb09fa426287d37f446b3123329e9b7bf46d88dda726ff4be9a3`.
- `SelectedResidualHighRecovery`: `2924bf616df3fdaefd952b61f4ee78c61ef961d605cc7407282692c41b133abc`.
- `SelectedMiddleComponentClaimsV2`: `ce588a03c2bd22f745faac7344e4f7589f2d4c95c79c6df29638486e4a455ff3`.

All are previously green predecessors. The retained focused command used
Lean 4.32.0 with `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB,
SwapMax 0 and CPUQuota 200%. Exit status was 0, wall time 3.20 s, peak RSS
6,877,580 KiB and swaps 0. Exact command, source/output hashes and provenance
are in `experiments/selected-ordinary-row-acceptance-v4.log` and its frozen
manifest/source companions. The failed v1-v3 attempts remain on the NUC;
v4 removed the unused union wrapper whose decidable-instance mismatch did
not affect the umbrella acceptance bridge.
