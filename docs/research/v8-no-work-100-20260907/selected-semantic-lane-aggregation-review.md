# Selected theta and equality-point aggregation

Status: **GREEN and frozen**, with twelve standard-only axiom audits.
Checked source: [SelectedSemanticLaneAggregationV2.lean](experiments/SelectedSemanticLaneAggregationV2.lean),
SHA256 `94b291fa5efaf8de38a19bfa043b265585396bf53ad47a065c7465fe495ccbf3`.
It imports only the checked `SelectedSemanticHelperAggregationV2`. The failed
V1 is retained unchanged as a diagnostic. Both focused checks ran on the
capped Tailscale NUC; there was no local Lean invocation, new V5 cache closure,
or package replay.

## Exact statement and fixing order

`RowLanes` contains four Poseidon values, twenty-four packed semantic values,
and one copy residual. Its vector places them at powers 0..3, 4..27, and 28.
`eval_append` proves the concatenation symbolically; `selected_row_eval`
identifies the ascending-power expression for the source's two reverse-Horner
loops. `rowPolynomial_zero_iff` proves that zero as a polynomial is equivalent
to all 29 coefficients being zero, not that one zero evaluation suffices.

`badTheta T lanes` chooses one nonzero row polynomial, if one exists, from the
fixed 1,024-row table before theta. It is empty if every row polynomial is
zero. `badTheta_card` gives at most 28 roots in the original theta domain.
`theta_zero_or_collision` converts a zero theta-batched table into all-row
coefficient zero or this exception. There is no row-count multiplier.

After theta, the table's multilinear extension uses ten Boolean coordinates
in actual big-endian order: coordinate zero is physical row bit nine.
`sourceEqualityValue_booleanTracePoint` proves the literal equality-value
formula gives these row weights. Boolean interpolation proves a nonzero table
has a nonzero extension; its total degree is at most 10. `badPoint_fraction`
bounds the named point exception by `10 / |K|` on the full `K^10` domain,
with the zero-table branch assigned the empty exception.

`source_zero_alternative` consumes the exact zero sum of

```
equality_weight(row) * theta_composition(row)
  + mu * helper(row)
  + mu^2 * (1 - active(row)) * helper(row).
```

It returns either all 29 lanes zero on every row and both helper totals zero,
or theta belongs to `badTheta`, or the point belongs to `badPoint`, or mu
belongs to the already-checked quadratic `badMu` set. The separate bounds are
28 roots, a `10/|K|` fraction, and 2 roots. The statement does not sum these
into a probability of source acceptance.

The same-table quantities may depend on the entire prefix through lambda,
chi, and adaptive C2, but are fixed before theta. The point polynomial may
depend on theta, but not on the subsequently drawn equality point. The three
mu coefficients may depend on theta and that point, but not on mu. All later
messages and claimed openings remain unrestricted by this leaf. The sets'
arguments express these fixing boundaries without a retrospectively selected
row or target. There is no independence or Fiat--Shamir freshness assertion.

## Reused V7 proof and source pins

The narrow Boolean/MLE proof slice is ported from
`AspisFormal/V5AcceptedTerminalResidualExtraction.lean`, from
`bigEndianBits_injective` through
`uniform_zerocheck_collision_fraction_le_ten`. Its broader terminal model has
25 lanes and a linear helper and is deliberately not imported or reused as
the selected terminal statement. The original definitions are in
`V5ComponentADeployedTerminalApplicability.bigEndianBit/mleRowWeight`.

Local inspected bytes:

| Source | SHA256 |
| --- | --- |
| `AspisFormal/AspisFormal/V5AcceptedTerminalResidualExtraction.lean` | `eb97aebf1b6da90efba310f1dc6aa27965709a1fa5362dd1d4200352a11138ae` |
| `AspisFormal/AspisFormal/V5ComponentADeployedTerminalApplicability.lean` | `d264396204436546e97ff006994f32e9c6df1eb44c0f272c7d990d1634060b40` |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` | `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58` |

The Rust interfaces are `composition_parts` (line 1215) and `terminal_parts`
(line 1285). The code initializes from the copy residual, folds the 24 semantic
lanes in reverse order, then folds the four Poseidon lanes in reverse order.
The Boolean-row mathematical spelling is not a verified Rust execution
refinement. `SelectedSemanticRowsV3` separately supplies the selected 95-row
base packing; connecting all 24 zero packed semantic lanes back to those rows
uses its checked `packedRows_zero_iff`, but no such same-table authentication
is invented here.

## Falsifiers and remaining bridges

The one-point inference is false: a nonzero row polynomial such as
`X - theta0` vanishes at theta0. If a table were allowed to depend on the
current theta, the adversary could choose that example at every theta. This
is why `badTheta` fixes its row and polynomial before theta.

A nonzero Boolean table can have zero MLE at a non-Boolean point; its
multivariate root exception cannot be removed. The checked helper regression
`1 - mu^2` already establishes that the selected mu term can have two roots,
not the older V7 one-root charge. These are exact algebraic controls, not
accepted-proof or payment counterexamples.

The next consumer must establish that compact ten-round masked sumcheck and
authenticated openings imply the displayed Boolean zero sum, or one of the
explicit sequential degree-27 repair / mask / terminal authentication
alternatives. It must use the actual compact omitted-c1 grammar and causal
history-indexed message plan. All base-table, Poseidon, copy, slot-pole, and
initial-mask authentication obligations remain separate. The old `35/|K|`
terminal or `305/|K|` aggregate is not used. No global 40 or 310 subtotal,
payment extraction, or FS bound has been proved by this leaf.

## Focused build evidence

Research checkpoint parent: `8761cd89ab7ccea779ef4a9f86fa415d670bd16d`.
The inherited runner/cache bootstrap remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, with borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. These are deliberately different
provenance fields. Lean 4.32.0 ran `-j1 -M9500` in a separate cgroup with
8 GiB MemoryHigh, 10 GiB MemoryMax, SwapMax=0, and CPU quota 200%.
Module limits stayed at recursion depth 200 and 200,000 heartbeats.

| Target / tag | Exit | Wall | Peak RSS KiB | Swap | Audits |
| --- | ---: | ---: | ---: | ---: | --- |
| `SelectedSemanticLaneAggregation` / `selected-semantic-lane-aggregation-nuc-v1` | 1 | 3.69 s | 6,672,104 | 0 | diagnostic only |
| `SelectedSemanticLaneAggregationV2` / `selected-semantic-lane-aggregation-v2-nuc-v1` | 0 | 3.88 s | 6,704,336 | 0 | 12 standard-only |

V1 exposed a pointwise function-zero target, an unparenthesized product
binder, and recursion in the final nested `Or` packaging. V2 fixes those
three issues, moving only the propositional composition into the generic
`staged_alternative` lemma. No mathematical premise or resource cap changed.
That helper has no axioms; the other eleven audited theorems use subsets of
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
There are harmless unused-section-variable/simp and deprecated-alias warnings.
Both green provenance checks match all 1,057 pinned source/output entries.

| Artifact | V1 SHA256 | V2 SHA256 |
| --- | --- | --- |
| source and frozen snapshot | `97dbc36af38a75c72e80565f3822c4b23aa3ee35ea7c6e406c4cf6cefd09a299` | `94b291fa5efaf8de38a19bfa043b265585396bf53ad47a065c7465fe495ccbf3` |
| log | `ea2ef6ee524e54bed48b325015ec8fa29f9c6789aa49f1b087bdfbc462023a90` | `8977c376ab703161a1ddf49c7ef8878fa1f0d619f5e55893ec1fb49262ff7fdb` |
| manifest | `219bdb0ef0b342366f73eaca0bb4934b5de43ed85a72ce68877c30e6276b2750` | `f6b57562bcab9b84baed6dbea510a6d454bcceec0318555ab873b9188747e54f` |
| checked output | none credited | `bf6671439829fb68d2201b760c4ca7a291f13f56019b6b51762b6b519b6187f8` |

The source files, exact snapshots, logs, and manifests are local. The ignored
V2 olean is also locally hash-checked but is not required in a clone.
`experiments/audit_selected_semantic_lane_aggregation.py --check-recorded`
audits the retained evidence without rebuilding; its exact receipt is
`experiments/selected-semantic-lane-aggregation-evidence.json`.
