# Selected semantic aggregation: causal audit and helper step

Source parent: `d879105131a34a4bd087409bced83778d3ea8a96`.
GREEN and frozen: the focused source is
[SelectedSemanticHelperAggregationV2.lean](experiments/SelectedSemanticHelperAggregationV2.lean),
SHA256 `9d4151db2e593230dc0a5477df18c975f38eee9e2eaee4dfaf71e6a87cf1e50e`.
Eight audited declarations use only `propext`, `Classical.choice`,
`Quot.sound`. The V1 diagnostic is preserved, not counted as a green leaf.

## Literal selected schedule

The compact verifier uses `v6_transcript.rs`, not the full-28-coefficient
wire described at the top of `state_only_sumcheck.rs`.

| Order | Source action and fixing boundary |
|---|---|
| C1, lambda, chi | `begin_v7_compact_transcript_with_hiding_context` absorbs C1 before ordinary lambda and chi. C2 may depend on both. |
| C2, theta | C2 is absorbed before `begin_state_only_zerocheck`; registry and zero helper-sum bytes precede ordinary theta. |
| Equality point, mu | Ten ordinary equality coordinates follow theta; ordinary mu follows all ten. C2/helper values must already be fixed. |
| Initial claim, eta | `begin_state_only_masked_sumcheck` absorbs degree/round/initial-mask-claim bytes, then samples nonzero eta. |
| Ten semantic rounds | Each round supplies c0 and c2 through c27. The verifier reconstructs c1 from the current boundary, absorbs the framed 27 values, then samples that round's ordinary challenge. The challenge updates the running claim. |
| Point openings and terminal | Three point-claim groups are decoded. The caller compares the running claim with the selected masked terminal before gamma. Later relation/PCS authentication must bind these openings to the same earlier tables. |

Relevant exact source locations:
[v6_transcript.rs](../../../crates/aspis-core/src/v6_transcript.rs),
`begin_v7_compact_transcript_with_hiding_context` at line 317 and
`verify_compact_semantic_sumcheck` at line 399;
[state_only_sumcheck.rs](../../../crates/aspis-core/src/state_only_sumcheck.rs),
`begin_state_only_zerocheck` at line 80;
[state_only_hiding.rs](../../../crates/aspis-core/src/state_only_hiding.rs),
`begin_state_only_masked_sumcheck` at line 377.
Only this semantic segment is compared with V7; no equivalence of the
different downstream V8 OOD/gamma order or complete transcript is inferred.

## The old 35/K algebra bound does not instantiate

The actual pair-forest terminal has four packed Poseidon lanes, 24 packed
semantic lanes, and one extension-valued copy lane. The reverse Horner loops
in `pair_forest_semantic_terminal.rs::composition_parts` place Poseidon at
theta powers 0–3, semantics at 4–27, and copy at 28. The opt-in positive
transfer residual adds source position 94 to packed group 23, slot 2, hence
theta power 27; it does not increase the total of 29 lanes. The base crate
has positions 0–93, whereas the positive profile has 0–94. There are 95
semantic coordinates at each Boolean row, not 95 independent extension
coordinates at off-domain points.

The same file's `terminal_parts` computes exactly

`eq(zc,z)*composition(z) + mu*H(z) + mu^2*(1-active(z))*H(z)`.

Therefore its Boolean sum is

`C + mu*B + mu^2*I`,

with C the equality-weighted composition sum, B the total H sum, and I
the inactive H sum. H may be selected with C2 after lambda/chi, but not
after mu. The old `V5SequentialTerminalChallengeBound` uses 25 lanes and
only a linear helper: its 24+10+1=35 coefficient budget is inapplicable.
The corresponding selected fixed-table budget would be 28+10+2=40,
subject to the missing source/causal adapters below. This report does not
claim that full probability theorem has been checked.

The existing registry payload still carries its own state-only constants
(including 102 copy links); those bytes are not a proof that the selected
136-link row registry equals the older layout. Source/release/profile
correspondence must be tracked separately. The new proof does not import
the old fixed layout as the selected one.

## Falsification and the smallest surviving theorem

One active row with H=1 and one inactive row with H=−1 has B=0 and I=−1.
Choosing weighted composition sum C=1 gives `1−mu^2`. At mu=1 and mu=−1
the aggregate vanishes although C and I are nonzero. When characteristic
is not two these are distinct roots. Thus neither unconditional coefficient
recovery nor a one-root helper bound is valid. This is an exact additive
source-shape regression, not an accepted complete proof or local-copy-row
fixture.

The new leaf constructs the polynomial from the three actual coefficients
using the pinned V7 `monomialPolynomial` representation. It proves:

- `source_sum`: the displayed Boolean table sum equals evaluation of that
  polynomial; the row set and weights are symbolic, allowing all 1024
  selected rows without enumeration.
- `aggregate_zero_iff`: polynomial identity is equivalent to C=B=I=0.
- `badMu_card`: the constructed root set in the original mu domain has at
  most two elements, and is empty when the polynomial is identically zero.
- `source_zero_or_collision`: zero aggregate yields all three coefficients
  zero or membership in that exact collision set.
- `collision_continuation_bound`: any later reward bounded above by one,
  gated by zero aggregate with some nonzero coefficient, has finite uniform
  mean at most `2/|S|`. Rewards may depend on mu; the coefficients may not.
- `quadratic_regression` / `regression_two_roots`: the two-row example and
  both distinct roots above, with the nonzero characteristic-two guard.

The sole import is the existing `JointImageGame`, reusing its V7 polynomial
coefficient/degree API and exact finite root bound. No additional V7 cache
closure, old global numeric ledger, or source authentication assumption is
needed for this bounded leaf.

## Total causal theorem target and exact remaining premises

The surviving upstream target is a total event inclusion, not
`one accepted aggregate implies all rows`:

`accepted semantic wire → same-table row/copy conditions OR
 authentication/projection failure OR adaptive round repair OR
 theta collision OR equality-point collision OR quadratic-mu collision`.

Here same-table row/copy conditions mean all 95 Boolean semantic residuals,
the actual selected Poseidon gates, local selected copy rows, and both total
and inactive H sums. Slot-pole exclusion is an additional copy condition;
it cannot be manufactured from the multiplied local copy equations. The
existing lambda/chi copy collision analysis may then be consumed once,
provided its same early-family/table hypotheses and poles are supplied.

The selected helper leaf is the mu step of this target. To finish it:

1. Use one C1 table fixed before lambda/chi, an adaptive C2 fixed before
   theta, and their source-shaped mask/helper functions. A table selected
   only after theta or semantic challenges cannot receive a one-table root
   bound retrospectively. A prior fixed candidate family requires explicit
   capture and union accounting.
2. Derive the selected 29-lane coefficient representation and the nonzero
   theta-polynomial bad set (at most 28 roots). The already checked
   `SelectedSemanticRows.packedRows_zero_iff` then separates the 95
   base-valued semantic coordinates. Actual Poseidon projection to its
   block-round conditions remains a separate source identity, not a supplied
   arbitrary Poseidon oracle silently treated as genuine.
3. Reuse V7's generic `tableMLEPolynomial` / nonzero / totalDegree≤10 /
   `uniform_zerocheck_collision_fraction_le_ten` for the SAME theta table.
   That is a ten-coordinate fresh-law calculation, not ten independent
   postselected bad sets. Apply the checked quadratic helper step after it.
4. Instantiate `V7CompactSemanticBinding.compact_acceptance_boundary_or_three_named_failures`
   for the matching compact round grammar. Its alternatives retain
   `MaskInitialClaimAuthenticationFailure`,
   `FixedTerminalOpeningAuthenticationFailure`, and `TenRoundRepair`.
   Eta/source mismatch must also be retained if not identified by the actual
   projection. Neither initial-mask nor terminal-opening authentication
   follows merely from the terminal callback returning true.
5. Supply an actual prefix-causal `WireUsesAdaptiveDegree27Plan` and fixed
   reference trace, then use `V5AdaptiveSumcheckChallengeBound`'s 270/K
   sequential repair theorem. Together with the proposed selected algebra
   step this suggests 310/K for one fixed table, not the old 305/K, and
   still excludes authentication/copy/freshness costs. No such complete
   selected bound is asserted here.

The authentication caveat is necessary: the callback's explicit G opening
has a known linear coefficient in `state_only_selected_mask_value`. If that
coefficient is nonzero and the opening is unconstrained, it can be chosen
after the semantic challenges to force the scalar terminal equality without
changing any previously fixed bad table. The real PCS/claim-binding layer
must rule this out; this observation is not a forgery of that layer.

The V7 reuse map is thus exact but limited:
`V7Tag73SemanticRoundReplay` and `V7Tag73AcceptedSemanticExecution` provide
matching semantic event/round framing; `V7CompactSemanticBinding` provides
the reconstructed-message boundary; `V5MaskedBoundaryFailureAccounting`
names the unresolved authentication and repair events; generic V5 MLE and
adaptive-degree27 arguments provide candidate counting ingredients.
`V7AcceptedSemanticRelationComposition` hardcodes the older lane family,
and `V7DeployedCopyEvaluatorBalanceBridge` the older copy layout: neither is
the selected 95/136 source adapter.

No ROM/FS freshness, full witness extraction, verification acceptance,
transcript change, byte reduction or CU result is claimed by this leaf.

## Audited source hashes

- `crates/aspis-core/src/v6_transcript.rs`: `48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf`.
- `crates/aspis-core/src/state_only_sumcheck.rs`: `5458d3134a3123b8b02bef0374ccbf96a05461974d7e274966c6a3f0d2d496f9`.
- `crates/aspis-core/src/state_only_hiding.rs`: `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f`.
- `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`: `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`.
- `experiments/positive_transfer.rs`: `f5031b80ff2d9f40689f2bd6d18323be330664bedd0aec24b34bd67aeeea12a8`.
- `V5AdaptiveSumcheckChallengeBound.lean`: `230b868cd3f423cff665eb132b091a551c0d591f20380c7b40fc333fc201cf9e`.
- `V5MaskedBoundaryFailureAccounting.lean`: `36a10a0fbfdcd0169feff0b2d650a4c83be40e521f1f36447654d713302b4566`.
- `V5SequentialTerminalChallengeBound.lean`: `9808f2aef0b21553f0e1d620ec790636ecdc5d5ca3e8e766aabf5b12da4650f6`.
- `Pool/V7CompactSemanticBinding.lean`: `cef187756e6c396df2a636368f852e5a6f71f32e4127089b4b453d3ed86335eb`.
- `Pool/V7AcceptedSemanticRelationComposition.lean`: `927550becfa4487728e7fe7620c9a26b882987ed11138c4cc26d8dbf3c191b78`.

These are source-inspection hashes, not claims of fresh proof builds.
Metadata's read-only check found the four proposed broader V7 imports absent
from its retained 1035-entry manifest; that does not by itself prove remote
cache absence. No cache mutation or broad replay was attempted for this task.

## Frozen focused evidence and reproducibility

Both attempts used the inherited higher-Y runner over Tailscale, Lean 4.32.0
with `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPU 200%, depth 200 and heartbeats 200000. Runner bootstrap/cache parent
`289d7356c78a4cd493fe61a54f9548f2a0c11298` is distinct from the source parent
above; borrowed V7 pin is `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The local frozen runner hash is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

| Target / tag | Exit | Wall | Peak RSS KiB | Swaps | Provenance |
|---|---:|---:|---:|---:|---|
| `SelectedSemanticHelperAggregation`, `selected-semantic-helper-aggregation-nuc-v1` | 1 | 3.16 s | 6658724 | 0 | 1051 preflight |
| `SelectedSemanticHelperAggregationV2`, `selected-semantic-helper-aggregation-v2-nuc-v1` | 0 | 3.38 s | 6689556 | 0 | 1051 unchanged |

V1 failed on three local elaboration seams: simplifying the three zero
coefficients, simplifying the total zero callback, and matching a Nat-cast
two to a rational two. V2 explicitly expands only the three coefficients,
proves the callback equality pointwise before averaging, and normalizes the
small Nat cast. No definitions, mathematics, budgets or resource limits
changed. Four unused-section-variable warnings remain in V2. No unchanged
target was rerun, and no dependency or local laptop build was launched.

All triplets and the optional green olean are local and hash-checked:

- V1 source/snapshot `379c4e50ccacb1059472f3a7a2c44095516d3ac418e977c392b32fae4320db37`;
  log `18632db9febf7652afb5d53d79ba40d2d5d6565c2a66532d5fb3d77d77edb5ad`;
  manifest `a9daf91dea8b7e59d9d17f09c776fd09864abc2cf302adc8aef65af8b55d4dd7`.
- V2 source/snapshot `9d4151db2e593230dc0a5477df18c975f38eee9e2eaee4dfaf71e6a87cf1e50e`;
  log `4f975b92732bf3e83e055b64c38c49168d524bfeabb98964635ca979d28e0d64`;
  manifest `59b3fb0dbe27eb1cd02abaf06e3dd339ca52d704865ce75ef0227cc5e7f58b79`;
  olean `f0d7ecee3edd304fc8ffd59ea385f2e1c1a603c2877181a90e427b439dd26c45`.

The read-only auditor and JSON receipt validate source/snapshot equality,
commands, caps, resource measurements, manifests and every printed audit.
Ignored oleans are checked when present but are not required on a clone:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_selected_semantic_aggregation.py --check-recorded
```

The scoped file set is two Lean versions, two source/log/manifest triplets,
this report, the read-only auditor, and its JSON receipt. No other agent's
source, stopped-prefix/termination work, or frozen proof was edited.
