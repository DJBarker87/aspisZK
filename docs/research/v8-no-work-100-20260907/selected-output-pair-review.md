# Decoded output notes feed a checked transfer pair

Research source pin: `e90e7338656f221c9a1bbde90d533ba94d002014`. This dependent leaf consumes the newly checked [output-note openings](selected-output-notes-review.md); their exact source and olean hashes are pinned by its runner. Existing green sources are unchanged. No Rust, production default, masking, transcript or verifier operation is changed.

## Concrete compiler branch addressed

`pair_tree_profile.rs:199–221`, `PoolV1PairLeafWitnessV1::two_outputs`, rejects a zero last limb of the change commitment before constructing its inverse and validating the occupied pair. The previous output-note hash theorem alone did not rule out that rejection. A correct output hash is not a nonzero-sentinel assumption.

The selected transfer constraints already supply the missing information:

| Actual selected obligation | Leaf hypothesis/use |
|---|---|
| Occupancy row1018, source lane11: `occupied-1=0` | Derives occupied=1; transfer-specific, not withdrawal. |
| Same row, source lane1: `sentinel*inverse-occupied=0` | Together with occupied=1 gives a genuine inverse certificate. |
| Copy tag1124073492: row523 c0–7 → row1018 c2–9 | The certificate belongs to the actual change digest; c9 is its last limb. |
| Copy tag1124073493: row475 c0–7 → row540 c0–7 | The recipient digest is block33's rate chunk. |
| Copy tag1124073495: row1018 c2–9 → row528 c8–15 plus last-limb offset1051521018 | The same change digest is block33's high input, with the node tweak removed. |
| Block33 row528 c0–7 zeros and eleven row-pair residuals | Constructs the actual modeled node input and round chain to final row539. |

These are a **sufficient subset** of individual source residuals, not a deletion of the other occupancy, schedule, padding or masking checks. Recipient/change tags3492/3493 are enabled with weight one for transfers. Tag3495 is unconditional. All table values may be adversarial; no honest trace, successful compiler, valid witness, chosen-salt success or nonzero digest premise is assumed.

The compiled occupancy expressions are in `pair_forest_semantic_terminal.rs:522–603`; the source transfer variant gives expected output occupancy one. The node initial selector covers block33 (`nodes = [4..25,33..57]`). The frozen copy patterns and links are in `pair_forest_copy_terminal_constants.rs`. `pair_trace.rs:651–682` constructs the two-output pair and block33 before the late append. The source relation-free mask registry does not replace any of the specific constraints consumed here.

## Proved interface shape

`SelectedOutputPair.lean` derives the chain:

```
occupancy equations + actual change copy
  → change[7] * recorded inverse = 1
  → valid two-occupied-output pair and change[7] ≠ 0
  → recorded inverse equals the computed field inverse
  → the modeled two_outputs field-stage constructor returns a checked pair

actual recipient/change copies + node low zeros + block33 pair residuals
  → block33 input = nodeState(recipient,change)
  → recorded row539 = nodeHash(recipient,change).
```

`actual_change_sentinel_nonzero` reuses V7's `valid_occupied_second_sentinel_ne_zero`. `nonzero_two_outputs_checked` reuses the existing V7 occupancy constraints and `SelectedPairDecoder.v7_valid_implies_field_validator`, including its defensive occupied-sentinel check. `node_absorption_from_cells` is a generic rate-eight node-input identity; the selected theorem supplies its actual cells through the proved copy aliases rather than assuming the hash input is correct. `blockRoundChain` and `node_gate_forces_compression` then reuse the checked deterministic round/sponge infrastructure.

The literal compiled offset is retained in `OutputPairResiduals.rightCopy`. Its equality to the negative node tweak is proved using the exact small symbolic cast argument from pinned `V7MerkleLevelFromTrace.right_offset_cancels_node_tweak`: the two natural constants add to the characteristic. The old module's unrelated extraction closure is not imported, and no giant field reduction is run.

`public_output_pair_endpoint` transports independently supplied public recipient/change binding residuals. `decoded_outputs_feed_checked_pair` consumes the green bounded-canonical-table/raw-output-note theorem on the **same table**, giving both decoded note openings, a checked field-stage output pair and its recorded node hash. Public asset/commitments remain independent inputs whose authority is not fabricated from the C1 columns.

## Scope and remaining obligations

`twoOutputsFields` models the constructor after the raw M31 canonicality check: sentinel rejection, computed inverse and the modeled field validator. This is not an automatic Rust translation or a theorem that the complete compiler returns `Ok`. Concrete M31 inversion/parsing, actual Poseidon pair evaluator/constants, and their correspondence to the maintained field/`gateStep(rc)` model remain source interfaces. The final raw theorem includes the canonical C1 precheck, but public statement/context authenticity remains external.

The result closes the **modeled output-pair constructor/hash slice**, not append or settlement. The next deterministic step is the late append rooted at row539: connect the selected append copy choices and public snapshot/frontier to the exact next-root/frontier/index/sequence afterstate. The input owner/note/nullifier, 24-level recorded path, input occupancy and strict decoded amounts have existing modeled endpoints and should not be described as wholly unproved; their common raw record/source/caller-context composition remains necessary.

Accepted-proof enforcement of the individual residuals, authenticated/replay C1 recovery, adversary resources, Fiat–Shamir and full-view hiding remain separate. This theorem adds no probability term or security bits. The **40,282-byte maximum** and verifier CU are unchanged; there are no new messages or verifier operations.

## Focused evidence

Status: **formal proof complete for the stated modeled residual-to-pair endpoint**. The source and all twelve endpoint audits passed the root-serialized focused check. No dependency rebuild, Rust test, SBF job or benchmark was performed.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_output_pair.sh \
  docs/research/v8-no-work-100-20260907/experiments/selected-output-pair-v2.log
```

The runner verifies imported source/olean provenance (including the newly green `SelectedOutputNotes`), uses the existing `.selected-forest-cache`, and bounds the process tree with the7,340,032-KiB RSS guard plus Lean `-M7000`. Only the new leaf was compiled.

| Focused attempt | Exit | Wall | Peak RSS | Swaps | Result |
|---|---:|---:|---:|---:|---|
| [v1](experiments/selected-output-pair-v1.log) | 1 | 12.14 s | 5,478,187,008 B | 0 | Two local dependent-if simplification errors in the generic node-input lemma. Occupancy, inverse, constructor and copy aliases elaborated; the failed dependent endpoint was not claimed. |
| [v2](experiments/selected-output-pair-v2.log) | 0 | 11.32 s | 5,638,799,360 B | 0 | Both symbolic branches closed; all twelve axiom audits use only `propext`, `Classical.choice`, `Quot.sound`. |

The v2 source change only supplies the omitted Boolean/dependent-if simplifications. It does not alter a hypothesis, relation, field law or theorem statement. No larger memory cap or unchanged replay was used. The failed log's elaborator-generated `sorryAx` entries are diagnostics of the rejected v1 check; **none appears in the green endpoint** and no `sorry` or new axiom occurs in retained source.

- Source SHA-256: `cdce2ed893d0d1e87ad1e838df2ea9dd9c1d19409e5053d0be6d93749616e4e1`.
- Olean SHA-256: `20fec171072bb15bc8821946917fdaa81bd73fc2397d3a5c2a5786e3cb5a7208`.
- Toolchain: Lean4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, arm64 macOS; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.

The exact commands and old/new source hashes are in the two logs. Imported sources are pinned, and the new output-note dependency is byte-identical to its earlier green source/olean pair. No real witness is evaluated or printed.
