# Same-table checked output pair and append transition

Status: GREEN, first focused attempt, ten standard-only axioms audits. Source parent
`d879105131a34a4bd087409bced83778d3ea8a96`; borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

## New deterministic implication

`SelectedSemanticOutputTransition.lean` extends the green positive-transfer
`TransferFacts` endpoint with one genuinely checked constructor slice:

1. Recover the three eight-limb copy equalities from the actual weighted
   aliases on `memberTable candidate`, including the final-limb offset.
2. Extract output occupancy and inverse equations at row 1018 from the whole
   95-position Boolean oracle, and the initial low-half zeros at row 528.
3. Together with the existing block-33 Poseidon gates, construct
   `SelectedOutputPair.OutputPairResiduals` on **that same** `semanticTable`.
4. Reuse V7 occupancy validity to derive the change commitment's nonzero
   sentinel. The actual field-stage `twoOutputsFields` constructor succeeds,
   computes its inverse, and its ordered pair hash is the table's append leaf.
5. With explicit `AppendResiduals` and direct `AfterstateChecks`, reuse
   `SelectedAppendAfterstate.public_output_pair_afterstate` to identify the
   complete next root, twenty frontier entries, and integer cursor increment.

No successful decoder, nonzero sentinel, honest trace, valid witness, or
accepted transcript is assumed. `semantic_transfer_transition` also obtains
the earlier payment facts from the same residual oracle rather than assuming
them. `member_transition_or_copy_collision` preserves the actual pre-lambda
EarlyC1 family member and one sequential lambda/chi collision alternative;
all four slot poles and both helper boundaries stay in `CopyConditions`.

## Exact selected source mapping

| Index / tag | Weight in transfer | Actual eight-limb mapping |
| --- | --- | --- |
| 20 / 1124073492 | transfer = 1 | row 523 / columns 0–7 → row 1018 / columns 2–9 |
| 21 / 1124073493 | transfer = 1 | row 475 / columns 0–7 → row 540 / columns 0–7 |
| 23 / 1124073495 | constant 1 | row 1018 / columns 2–9 → row 528 / columns 8–15, plus 1051521018 on the last limb |

Withdrawal-only link 22 is not substituted for link 21. The source offsets
and patterns are checked against the existing literal 136-entry registry;
only three static metadata entries use scoped depth 1000, matching the green
input-pair certificate. All field/table/decoder proofs remain at depth 200.

The source runtime slice is `pair_trace.rs::build_transfer_inner`, which calls
`PoolV1PairLeafWitnessV1::two_outputs` after checking the two output note
commitments. `SelectedOutputPair.twoOutputsFields` retains the field-stage
sentinel rejection, inverse computation, and `validatePairFields` branch.
Canonical parsing and concrete Rust/Poseidon implementation correspondence
remain external; this is not claimed as execution of the Rust validator.

Source SHA256 values:

- `pair_forest_copy_terminal_constants.rs`:
  `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50`.
- `pair_tree_profile.rs`:
  `8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2`.
- `pair_trace.rs`:
  `80290c5af3e8102da8e43efbadccfde745af272c2bfb046a919d5ce4da9f9371`.
- `pair_forest_trace.rs`:
  `0a97cbba7740acf44e3b85082ff917e6fb60b81a26662a2d7f96acaf0e72309d`.
- `pair_forest_semantic_terminal.rs`:
  `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`.

## Explicit remaining conditions

The append theorem's local weighted current-child equations, sibling bindings,
initial zeros and gates are still supplied through `AppendResiduals`.
`AfterstateChecks` retains sequence/index equality, integer capacity and
increment checks, static frontier checks, and dynamic carry/root bindings.
The empty-root array is the literal `SelectedSemanticRows.emptyRoot`, not a
supplied mathematically correct empty array. Its generated-hash correctness
and the bounded carry scan's Rust-intrinsic correspondence are not proved here.

The next source projection is to derive these append records from semantic
rows and links 24–63. Independent locked-live-state / pool / deployment /
asset authentication, historical input membership, nullifier freshness and
transactional custody effects are still needed for a complete payment-context
or settlement theorem. The endpoint does not certify those predicates by
packaging its conclusion as `TransferTransitionFacts`.

`V7DeterministicSpendWitness` is not directly substituted: its retained
one-input/one-output, old depth-20 opened-column relation differs from this
two-output, 24-level pair/lane/forest layout. `V7EightLaneForestTerminal`
requires exact membership, locked-lane source and append evidence; its
`ForestTerminalAccepted` record is not an acceptance-to-witness shortcut.
The new leaf instead consumes the already selected V7-reuse interfaces with
matching rows and patterns.

## Focused verification

Sole import: green `SelectedSemanticTransferV2`; no new V7 cache chain or broad
replay was needed. The parent ran the smallest target through the existing
Tailscale NUC runner, capped at
MemoryHigh 8 GiB / MemoryMax 10 GiB / swap 0, Lean `-j1 -M9500`, depth 200 and
250000 heartbeats except the isolated three-entry metadata check.

Exact tag: `selected-semantic-output-transition-nuc-v1`.
Exit 0; wall 3.59 s; peak RSS 6,729,444 KiB; swaps 0.
Both provenance checks passed with 1049 entries, unchanged. All ten printed
axiom sets are `[propext, Classical.choice, Quot.sound]`.

SHA256 values:

- Source and retained source snapshot:
  `9661416d3c81a21518c1837b08e1fc8a3cf807b991864817b1b6594d48294633`.
- Green olean:
  `f67b39ac8785e9062ad71462cc2f41af6449d787d06719d3d89108567e8634b7`.
- Log:
  `18eb4e74103abe97c18d44827d5116e7f016f4848cf5635836858455b8b43695`.
- Per-run manifest:
  `3ab00367760d259207201da78ef633297b415188ab648c22bc81bafcc0a698c8`.

The source parent above is distinct from the inherited runner bootstrap
`289d7356c78a4cd493fe61a54f9548f2a0c11298`. The native package/import cache
is a pinned artifact boundary, not an asserted cold recompilation.
Local source/log/manifest/snapshot and green output hashes were verified.

Recheck from the worktree:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_selected_semantic_output_transition.py --check-recorded
git diff --check
```

The new auditor reuses the frozen preceding read-only auditor, checks its
record, and matches all four retained green source/olean pairs to this
target's actual import manifest. It checks the five Rust source hashes,
exact command/caps/resources and ten audit names. The publication is
clone-portable: mandatory logs/manifests/source snapshots/JSON are checked
unconditionally; ignored local oleans only when present. No source edits,
cache mutation, broad replay or further compiler run followed the green check.
