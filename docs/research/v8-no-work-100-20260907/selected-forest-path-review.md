# Selected C1 path residuals to the decoded 24-level hash chain

2026-09-09. Research branch `research/v8-no-work-100-20260907`, inspected
clean at `15e73e9fdf529a0d0ab46353b98bccaf029bf4f5`. This consumes
[the selected pair decoder](selected-pair-decoder-review.md), without changing
that proof, the Rust verifier, the production protocol or the proof grammar.

## New result

[SelectedForestPath.lean](experiments/SelectedForestPath.lean) proves a
deterministic source-shaped path endpoint over the maintained M31 relation
field. Given its explicit subset of individual selected residual equations,
the siblings read by the actual coefficient-to-witness decoder, with its
actual direction bits, form all **24 consecutive parent steps**. Their fold
starts at trace row **59** and ends at trace row **907**.

The proof does not assume the trace was honestly produced, a valid witness,
successful decoding, a correct root, a permutation-correctness equation or a
supplied `RoundChain`. It constructs the latter from the eleven two-round
residuals of each selected node block. The root obtained here is the recorded
trace value, not yet the independently authenticated public anchor.

This closes the structural membership-path slice after exact residual
recovery. It does **not** close acceptance-to-residual recovery, Rust/Lean
Poseidon correspondence or the complete payment-witness endpoint.

## Exact selected layout and decoder correspondence

At level `l`, the source's auxiliary base is
`913 + 16*(l/4) + 4*(l%4)`. Its bit is column 0, its current digest is
columns 1–8, and the successor row contains left/right in columns 0–7/8–15.
The sibling is the left child when the bit is one, otherwise the right child.
This is the literal branch in `recovered_witness.rs::decode`, not a newly
chosen existential sibling or an additional trace column.

| Levels | Meaning | Node blocks | First/last relevant boundary |
|---|---|---|---|
| 0 | Private selected slot into its pair leaf | 4 | row 59 to row 75 |
| 1–20 | Twenty pair-tree membership levels | 5–24 | row 75 to row 395 |
| 21–23 | Three lane-to-forest levels | 54–56 | row 395 to row 907 |

The discontinuity at level 21 is essential: the current copy comes from
block 24's final row **395**, not block 53. The source's last three outputs
are rows 875, 891 and 907. `pinned_path_transitions` checks these small
indices; `all_node_cells_in_shape` and the reused auxiliary-range theorem
bound every selected node/decoder coordinate.

The three weight-one copy edges per level have literal limb equations:

```
previous block row11[0..8] = auxiliary current[1..9]
auxiliary left[0..8]      = target block row12[0..8]
auxiliary right[0..8]     = target block row0[8..16] - last-limb NODE_TWEAK
```

The right offset is exactly the registry's subtraction of `0x41531005`.
`absorbed_is_node_input` proves that the block's actual rate-eight absorption
restores the correct node input, using the selected **low row-zero constraints**.
The tweak is not dropped or assumed to cancel on honest data.

## Source map and exact hypotheses

The following are inspected source relationships at the pinned revision,
not claimed translated-Rust theorems:

| Source | Relationship to the new leaf |
|---|---|
| `pair_forest_hiding.rs:59,73,144` | Exact auxiliary/block formulas and 72 selected current/left/right copy edges |
| `pair_forest_trace.rs:429–462` | All three edge kinds are weight one; the right consumer removes the last-limb node tweak |
| `pair_forest_semantic_terminal.rs:394–426` | Selected path selector and 17 path lanes: Booleanity plus eight left/eight right gates |
| `pair_forest_semantic_terminal.rs:243–269` | Membership node blocks have their eight low initial lanes constrained to zero |
| `pair_forest_constraint_residuals.rs:325–341` | The individual base-field gated ordering equations, without a redundant sibling cell |
| `pair_forest_constraint_residuals.rs:229–245` | New blocks 54–56 use eleven row-pair residuals, adding row12 absorption only for pair zero |
| `poseidon2.rs:239–255` | Pair zero applies the leading external layer, then rounds `2*j` and `2*j+1`; the maintained `gateStep` has this same mathematical schedule |
| `recovered_witness.rs:44–69` | Canonical M31 precheck; 24 direction reads; pair slot, twenty lane siblings, three forest siblings |

`PathResiduals` requires, across the 24 levels, 24 Boolean equations,
384 selected-child equations, 576 copy-limb equations, 192 low initial-zero
equations and 4,224 pair-transition equations. This **5,400-equation subset**
is sufficient for the claimed path theorem; it is not the entire semantic
inventory and does not describe 5,400 newly added verifier operations.

In particular, high absorption-lane zeros, the other 33 permutation blocks,
the other copy edges, occupancy, value, note/owner/nullifier and public/runtime
constraints are not erased. The hypothesis concerns **individual** equations,
not merely a scalar challenge combination vanishing.

Allowed masks do not simplify these hypotheses. The node slice uses local
rows 0–12 and the auxiliary slice uses exactly the source-designated current
and children cells. Relation-free Poseidon padding is in local rows 13–15,
and the auxiliary mask map excludes these used cells. The inherited mask
invariance result remains applicable to the decoder read footprint; no new
adaptive hiding claim or requirement that the 3,803 honest masks equal zero
is introduced.

## Proof reuse and boundaries

| Result | Status and role |
|---|---|
| `selected_direction_decodes` | Reuses the previous fallible Boolean decoder lemma; successful parsing follows from the selected residual |
| `decoded_ordered_children` | Reuses V7's `gated_selected_child_forces_ordered_children`, then identifies its sibling with the literal decoder branch |
| `exact_copy_digests` | Derives all three exact digest aliases from the source-shaped copy residuals |
| `absorbed_is_node_input` | Proves the actual row-zero/row-twelve/tweak interface |
| `roundChainOfResiduals` | Constructs `TwoRoundPermutationRows` from the selected rows and reuses `toRoundChain`; uncommitted odd-round states are synthesized |
| `selected_parent_step` | Reuses `node_gate_forces_compression` and the decoded child order |
| `complete_selected_path` | Reuses generic `foldl_chain` at depth 24, not the old `Root` definition fixed at depth 20 |

The direct reuse is deliberately narrow. The old deployed path capstones
use 20-level input/output geometry and other selected-column conventions;
their accepted-path assumptions are not substituted for these new residuals.
`V5AcceptedSpendRelation` transitively imports the historical work-normalised
ledger, but this leaf uses only its **deterministic two-round conversion**.
No old soundness/work theorem or positive grinding credit enters the result.

The maintained `RoundConstants` remain parameters. Mapping them, the lazy
M31 arithmetic and the compiled pair evaluator to `gateStep` is the stated
code-constant/source correspondence obligation; the proof is not a Rust
translation. Kernel checking does not make an uninstantiated source boundary
true. No hash collision resistance is needed for the deterministic chain
identity itself.

The exact source does contain the next root-binding residual: host assembly
sets `public_bindings[0..8]` to row907 minus the supplied anchor, and selected
public-digest lanes bind row907 to `public.anchor`
(`pair_forest_semantic_terminal.rs:617,742`). The new leaf does not assume or
derive those residuals from acceptance. Even their vanishing must be paired
with the independent caller/account context; it must not manufacture an
authenticated root from prover-supplied public bytes.

The start at row59 is likewise a recorded input-note digest. Its equality to
the decoded owner-key/value/asset/salt note commitment is a remaining deterministic
slice. Prior amount/occupancy facts remain reusable, with the previously
recorded positivity gap unchanged.

## Focused execution and evidence

No Rust/SBF/prover benchmarks or unchanged proof suites were rerun. The
research-only runner checks source equality against both the pinned research
commit and the read-only main cache, records the imported project-source
closure and cache hashes, and invokes no dependency build. The maintained
cache's direct root hashes are pinned. One missing V7 gated leaf was exported
to a research-only cache; the other proof dependencies were reused.

```
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_forest_path.sh cache /absolute/NEW-cache.log
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_forest_path.sh leaf /absolute/NEW-leaf.log
```

The cache command is only for an absent export; it refuses an unchanged
replay. Lean 4.32.0, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
Jobs were serialized with the other agents, with Lean `-M7000` and an
independent aggregate-child RSS stop at 7,340,032 KiB. `/usr/bin/time -l`
statistics below cover the Lean command, not the runner's hash preflight.

| Evidence | Exit | Wall | Peak RSS (bytes) | Swap | Outcome |
|---|---:|---:|---:|---:|---|
| [cache-v1](experiments/selected-forest-cache-v1.log) | 1 | 0.09 s | 112,001,024 | 0 | Local package directory shadowed the inherited HashMerkleModel cache; no proof loaded |
| [cache-v2](experiments/selected-forest-cache-v2.log) | 0 | 6.22 s | 5,625,856,000 | 0 | Explicit research-only links to pinned inherited cache fixed lookup; two standard axiom audits |
| [leaf-v1](experiments/selected-forest-leaf-v1.log) | 1 | 3.22 s | 5,509,431,296 | 0 | One local finish-row normalization goal; failed placeholder audit retained, not accepted evidence |
| [leaf-v2](experiments/selected-forest-leaf-v2.log) | 0 | 3.31 s | 5,651,824,640 | 0 | Pointwise `Nat.add_assoc` closes row10+1=row11; nine final audits, no `sorryAx` or new axioms |

The successful final audits use only `propext`, `Classical.choice` and
`Quot.sound`, or no axioms for the small pinned index certificate. No memory
or heartbeat cap was raised. The root build slot was released after v2.

Final source SHA256:
`8f0248edf14e711cc50f5038c3968ae5e90fc9b6ba01aba2e5ad94a8ece8e409`.
Final olean:
`771e1c180ba3345f6e4579fed3bf7b03c308dc5004effcbd46105d2100537311`.
Runner:
`b6dae82866db408c3996993b1a4ee1acde40ce80f9dd1c6e1cc41c05db72f567`.
V7 gated source/olean:
`f1e40eac2a8971119e827777e0581292a11467a30f6529a08c2cebdbe08e687a` /
`f832d8a65a4eae27cceb5843a46942f017dd76495e562413f51e7be9f1b138b2`.
Its last source commit is `b996eeff84bc3202316e5ae64bc06c0522a876da`.
The reused two-round conversion's source is pinned in the logs and last
changed at `598fe3389ef492e10437e28c4c013507d405eb1a`.

## Decision

The membership path is no longer an unnamed future conversion: its exact
selected cells, decoded siblings, node inputs, intermediate rounds and
24-step trace chain are now connected by a kernel-checked theorem. The
critical probabilistic task remains obtaining those individual constraints
on the recovered C1, with correct early C1 causality and authenticated access.

One decisive next deterministic experiment is to instantiate the pinned
two-round M31 evaluator and its constants against this leaf's `gateStep`,
then connect the selected Boolean-row semantic/copy result to `PathResiduals`.
That would replace an explicit source-shaped interface with actual source
evidence; further honest path round trips alone would not do so.

The proof body remains **40,282 bytes**, with zero new transmitted values,
rounds or verifier operations. These Lean timings are not CU, prover time,
extractor time or evidence of full-view ZK/Fiat–Shamir security. No numerical
global security or complete-payment-extraction claim follows from this slice.
