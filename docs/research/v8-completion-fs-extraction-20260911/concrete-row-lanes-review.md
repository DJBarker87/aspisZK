# Concrete selected RowLanes

`SelectedConcreteRowLanes.lean` is a checked source-shaped Boolean-row
instantiation. It neither assumes a supplied
Poseidon residual oracle nor infers row vanishing from scalar acceptance.

| Aggregation indices | Constructed quantity | Actual source correspondence |
|---|---|---|
| 0–3 | Four packs of sixteen base-field `successor − two_round_output` residuals | `state_only_poseidon::evaluate_state_only_poseidon_oracle_projected`; signs match target minus predicted state |
| 4–27 | Existing `SelectedSemanticRows.packedRows` | `pair_forest_semantic_terminal::semantic_packed`, with positive-transfer delta at position94; structural position95 remains zero |
| 28 | Existing `SelectedSemanticRows.copyResidual` | `evaluate_with_selectors(...).residual`; not packed as independent base components |

The selected wrapper's `poseidon_selectors` uses blocks0–56, not the default
49-block constant in the reusable Poseidon module. Active local rows0–10
give eleven pair transitions; row11 stores the successor/final state and
row12 supplies the first rate-eight absorption. The explicit residual uses
the existing `pairState`/`gateStep` model, including the first leading layer.

The `/16`, `%16` argument is narrowly ported from V7's
`V7PoseidonRowsFromTrace`, with the correct 57-block bound. It does not import
or pretend applicability of V7's 49-block count. It proves all active pair
residuals by symbolic indices, without reducing 627 concrete pairs or large
round constants.

`AllRowsZero` of these constructed lanes implies:

1. `RowsVanish` of the same semantic C1 table;
2. `PoseidonChecks` of that same table;
3. the selected copy residual vanishes at every Boolean row.

Packing injectivity is used only for four **base-field** coordinates lifted
into QM31. The copy lane and four extension-valued aggregation lanes are not
silently unpacked into independent base constraints.

`tupleLanes` takes one tuple and uses its C1 projection and lane26 helper.
It can therefore be instantiated with `recoveredComponents` without another
candidate or helper argument.

## Remaining source and causal work

- Prove the projected Rust Poseidon implementation equals these mathematical
  packed pair residuals at Boolean points, with the literal round constants,
  leading/full/internal selectors and canonical base-table correspondence.
  The source contains equivalence comments and differential tests; this new
  leaf is not their literal Rust refinement.
- Connect the positive profile's packed semantic implementation to the
  existing 95-position model. Do not apply this profile to unmodified94-lane
  source just because both pack into24 groups.
- Instantiate the masked semantic aggregation's lane table with `tupleLanes`
  at a causally legitimate point. A recovered table selected after theta
  cannot be declared fixed before theta by construction notation alone.
- Derive zero total H, zero inactive-H sum and every required slot non-pole
  condition separately. Row-zero does not imply these global prerequisites
  of `CopyConditions`.
- Keep masked semantic tables, full-view privacy and the acceptance-to-row
  exceptional alternatives in the composition. The new implication itself
  adds no probability claim and supplies no new security bits.

The final focused pinned Lean 4.32 run passed with only `propext`,
`Classical.choice` and `Quot.sound` (3.19 s wall, 6,553,972 KiB peak RSS,
zero swap). The initial missing-namespace failure is retained in the evidence
record. No fresh dependency/kernel replay was run. No protocol, proof-body or
production-source changes were made.
