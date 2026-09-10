# V7 atomic rows versus selected payment semantics

Source parent: `5cadd01c7af31a8ebe1a00e4bfed77c1e9c77b59`.
Status: `SelectedV7SemanticProjectionV3.lean` GREEN on focused attempt v4;
all ten audits are standard-only. Source and evidence are frozen. The three
earlier failed attempts and copy-only cache append are retained.

The useful overlap is62 scalar equations, not all selected payment checks.
[`SelectedV7SemanticProjectionV3.lean`](experiments/SelectedV7SemanticProjectionV3.lean)
constructs the physical trace from the SAME `semanticTable candidate`, and
derives the matching initial/padding fields. Its checked `semantic_projection`
completes `InputSemanticChecks` and `OutputSemanticChecks` only after their
genuinely unmatched fields are supplied. It is a semantic residual projection,
not another decoder or a theorem assuming a valid payment witness.

## What the accepted V7 theorem actually provides

`V7AcceptedSemanticRelationComposition.constraint_rows_vanish_of_compact_acceptance`
uses a coherent width29 extraction, an accepted compact Tag73 run, a fixed
ten-round oracle trace, authenticated initial mask sum and terminal opening,
and exclusions of `TenRoundRepair`, `HelperCancellation`,
`ZerocheckEvaluationCollision`, and `ThetaLaneCollision`. Its result is
`ExtractedConstraintRowsVanish`: independently supplied Poseidon rows vanish,
the literal old `AtomicSemanticRowsVanish` holds, and the separately supplied
copy lane vanishes. Neither Poseidon gate equations nor copy aliases are
derived merely by naming those independent functions.

This old atomic model has77 source positions packed into20 semantic QM31
lanes, hence25 constraint lanes including four Poseidon lanes and one copy
lane. The selected Rust model has95 positions packed into24 semantic lanes,
hence29 constraint lanes. Occupancy reuses positions0..11 on different row
supports. Its path17 positions occupy32..48, ranges33 occupy49..81,
conservation occupies82..83, public digests84..91, and scalars92..94.
An old compact-acceptance instance is therefore not automatically an
instance for the selected95-position oracle or its theta batching.

## Exact same-table comparison

Here “derived” means from the OLD atomic-vanishing hypothesis on the literal
finite restriction of `semanticTable candidate`, not from selected acceptance.

| Selected payment prerequisite | V7 support/formula | Projection status |
|---|---|---|
| `InputSemanticChecks.initialOwner` | full initial row0, owner domain/length8 | all16 equations match |
| `InputSemanticChecks.initialNote` | full initial row16, note domain/length18 | all16 equations match |
| `InputSemanticChecks.noteTailZero` | absorption row60, columns2..7 | all6 equations match |
| `InputSemanticChecks.initialNullifier` | old full nullifier row704; old path-initial low8 includes row400 | low8 match; selected row400 capacity8..15 remains explicit |
| `OutputSemanticChecks.initial` | old full output initial row736; old path-initial low8 includes rows432 and480 | low8 at each selected output matches; both capacity halves remain explicit |
| input/output `pairs` | Poseidon functions are independent inputs to V7 composition | no selected `BlockResiduals rc` expression correspondence proved |
| output `tailZero` | old low padding row780; selected rows476 and524 | no matching field |
| amount `boolean`, `recomposition`, `auxiliary` | old two-value range bases864/866, limb-value column10 and value column11; selected three-value bases1008/1010/1012, direct value column10 and six auxiliary zeros | no matching field; both locations and reconstruction organization differ |
| amount `first`, `second` | old fee balance row864: columns11−12−fee | selected conservation rows1014/1015 differ |
| all `InputPairSemanticChecks` | old atomic77 has no occupancy or private-direction bitness coordinates | no matching field; selected occupancy row1017 and direction rows913..1005 remain explicit |
| input asset/nullifier and output assets/commitments | old asset rows795/799; digest rows379/699/731/779 | selected assets44/460/508, nullifier427 and outputs475/523 differ |
| selected positive product-inverse pack | no old atomic77 coordinate | remains separate exact positive-pack premise |

The three complete input fields contribute38 equations; the nullifier and
two output low halves contribute24 more. `RemainingInputChecks` contains the
actual selected round-pair residuals and only the moved nullifier capacity
half. `RemainingOutputChecks` contains its round-pair residuals, both capacity
halves and both padding supports. The theorem does not weaken any selected
amount, input-pair or public-binding prerequisite.

The trace-shape bridge is constructive:
`physical candidate row column := semanticTable candidate row.val column.val`.
`physical_tuple_eq` proves
`physical (c1Projection components) = V7C1SubfieldRecovery.semanticTrace components`
by the actual first26/first16 column projections. No trace equality, support,
family membership or extraction success is an assumption of this identity.
Using a particular early family member still requires its identification
with this SAME tuple projection; it is not selected backward in time.

## V7 reuse and cache boundary

The borrowed source pin is `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

- `V7AtomicSemanticRowsFromTrace.coordinate_residual_zero_of_semantic_rows_vanish`
  is consumed directly. Source SHA256:
  `9b6dec4c38031c839b556af1b6cef935d743ad649be23ba299c3b004218076f7`.
- The initial specialization and low-padding proof are narrow ports of
  `V7HashBlocksFromTrace.initialResidual_at_retainedInitialRow`,
  `retained_initial_state_exact_of_semantic_rows_vanish`, and
  `low_absorption_padding_zero_of_semantic_rows_vanish`. Source SHA256:
  `bf4acde5ec688c50f48ea6baf667e2816e27b37b89e23b6eb67d0acdd1ba5dd3`.
- The low-half specialization ports
  `V7MerkleLevelFromTrace.initialResidual_at_pathInitialRow_low` and
  `pathInitialLow_zero_of_semantic_rows_vanish`. Source SHA256:
  `e8d9b76b1b46ef92266b79a8457ea8bf2048b3dc9565dab91764f5552d666009`.

The two large old trace/copy closures are not imported. Direct imports are
the atomic row leaf and the already-green `SelectedEarlyC1Inputs` and
`SelectedEarlyC1Outputs`. The atomic leaf and its four missing dependencies
were registered by an explicitly authorized copy-only append from the pinned
V7 native cache: `V7AtomicSemanticRowsFromTrace`, `V7OpenedColumnsFromTrace`,
`V5ProductionPublicResidualBinding`, `V5TowerPackedResidualExtraction`, and
`V5ConstraintLaneBatching`. Their exact source/output hashes, retained trace
hashes and all 48 prior standard-only audits are recorded in the
[append receipt](experiments/v7-atomic-projection-cache-receipt.json).

No native module was rebuilt. The script verified source bytes against the
borrowed Git pin, checked retained Lean 4.32.0 output headers and trace audits,
checked that no Lean/lake process was active, copied only ten nonexistent
paths, atomically changed the base manifest from 820 to 830 entries, then
verified it again. Green-output state stayed byte-identical. The five trace
JSONs and before/after manifests are retained beside the receipt. No `.ilean`
was needed for imports.

Four existing overlay outputs have the same pinned source but DIFFERENT
native olean hashes: `ArithmetizationCore`, `SoundnessLedger`,
`V5AcceptedSpendRelation`, and `V5FriConcreteEncoderApplicability`.
Their frozen variants were not overwritten. This is an explicit mixed-cache
artifact boundary, not a claim that all native dependencies were replayed
against this overlay. The focused consumer is the compatibility check;
native Mathlib/package artifacts remain revision-pinned cached dependencies.

Append evidence SHA256:

- helper: `f994d042341585345e33e11363b4ce728c06148d3a2e5957be98d91205b8fc33`
- before manifest: `38062882cab2675b5e39f292ea7770cf9aa9aef74da0c6eafff68d3907e69ac8`
- after manifest: `7a8880a79842ef97df07167f32a66e54873300342bc0f0a8975efd6974ff3df0`
- receipt: `df61e68c98381bd5d77ec4fbd6f3183673a0a9509a331d96cb417a35ad3b0048`
- unchanged green state: `9e8a01d9174fed60e5911d3f798849c160fb76436741ff651b755e30d9397168`

## Focused attempts

The inherited NUC scope is `aspis-higher-y.fMoMeX`, with bootstrap research
pin `289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from the current
source parent above. All attempts use Tailscale SSH, Lean 4.32.0, `-j1 -M9500`,
8 GiB memory.high, 10 GiB memory.max, zero swap allowance, and CPU 200%.
Runner SHA256:
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

| Tag / target | Result | Wall / peak RSS / swap | Proof status |
|---|---|---|---|
| `selected-v7-semantic-projection-v1` / `SelectedV7SemanticProjection` | exit 1 | 0.08 s / 184,452 KiB / 0 | overlay import absent; no declarations checked |
| `selected-v7-semantic-projection-v2` / same source | exit 1 | 3.28 s / 6,701,984 KiB / 0 | imported cache loads; first six audits standard-only, last four inherit failed `matching_checks` / `sorryAx` |
| `selected-v7-semantic-projection-v3` / `SelectedV7SemanticProjectionV2` | exit 1 | 3.38 s / 6,702,088 KiB / 0 | all index fixes pass; only two `change` failures remain because domain constants are irreducible; six clean audits, four inherited `sorryAx` |
| `selected-v7-semantic-projection-v4` / `SelectedV7SemanticProjectionV3` | exit 0 | 3.51 s / 6,735,764 KiB / 0 | ten audits use only `propext`, `Classical.choice`, `Quot.sound`; provenance 1017 unchanged |

The original source and both failed source snapshots are byte-identical,
SHA256 `4c18d848bca74033902ea1378abd691ea38048547c848905d1cc6ad3599222b0`.
Failed artifacts are retained; none is a green release.

- v1 log: `e06f30db52ea2decf4c1ecf5735f924efb7a761a1de7237fc443713fa2885624`
- v1 manifest: `e16b2827e6222d61be5cc1eef63f6e87c428876cb910fd37136ebbc135b0be12`
- v2 log: `fc74000712c347136df967ddae9a740f05d9b6fbdbf66ac5759f3a91f050028b`
- v2 manifest: `57c6d99c818d5df718fc13e5d56c0a6c3b553d477d9303091005a8006ba9e39b`
- v3 source: `e26d86dab9de31e41d1caec7af36c4ad529394d8094c96cd4cae7a9884798315`
- v3 log: `84a02e972c44d0c7401450bb94a675e95c8da61b494fbbfc0ed9e04f68096dac`
- v3 manifest: `f1b9a33decb0abfc712ebdbca04bb99d8ac5c5875dddadf0ff72cc9d0b79a105`
- green v4 source: `8c8652b2c2a5baf7ca2525f94646f40981f6f01323fb1de4ee17db4631b85d45`
- green v4 olean: `ebfd3d2bf4e36dbd56d970967b27165b35976c87dabb8b71ebc8f668f43d1694`
- green v4 log: `e6732d8d4b6cda69f7ec628599ffe22261758b7c67347a0996ded862c7610807`
- green v4 manifest: `c21a64ad4ff401326a1ad37ddf9f11472a9c1661a65c5b4e304702735b8b2eba`

The final repair explicitly simplifies the pinned irreducible `DOM_OWNER`
and `DOM_NOTE` definitions at two matching-row uses. No statement, resource
limit, copied cache variant, or generic proof changed. All four attempt
source snapshots, logs and per-run manifests are local. The green olean is
an ignored local artifact; its recorded hash is sufficient for publishing
the evidence without adding a binary cache payload.

## First missing source implication

The old theorem cannot establish the new amount or occupancy checks on this
table: for example, row1008 is not read by any old atomic coordinate. Changing
its bit0 to2 leaves the old atomic model unchanged but violates the selected
bitness equation `2²−2=0`. Likewise row1017 occupancy is not read. This is a
source-shaped non-implication, not an accepted selected proof counterexample.

The actual next bridge is to instantiate the existing sumcheck/batching
argument with a faithful **selected95-position Boolean residual oracle**,
including the row-selected reuse of positions0..11 and the three actual
openings `z`, successor and XOR12, then prove its coordinate projections.
The source mask/terminal-opening authentication and causal collision
exclusions must concern that same oracle and tuple. The initial/absorption
specialization proofs above are reusable, but the changed supports and lane
count cannot be imported by an assumed equality to the old oracle.

Even once those atomic checks are obtained, the selected Poseidon residual
functions must be identified with `BlockResiduals rc`, and compiled-copy
vanishing must feed its existing row/helper/pole conditions. Caller public
authority is not constructed from prover columns. Exact87 point claims alone
do not supply any of these semantic enforcement steps.
