# Selected sparse MLE and current/successor table reads

Source pin: `113dc5dacbf630c234cc6498385913507c171f8f` on the existing research branch. **The focused leaf is kernel-checked.** This leaf changes no Rust, protocol grammar, masking layout, transcript, defaults or proof body. The maximum remains 40,282 bytes.

## New deterministic endpoint

`experiments/SelectedSparseMle.lean` models the literal field/list algorithms for the selected sparse MLE helper and optimized successor. For arbitrary supplied 1,024-entry amount and inverse columns, the modeled positive last pack at Boolean row 1014 is zero **if and only if**

```
amount[1014] * amount[1015] * inverse[1014] = 1.
```

The inputs to that pack are obtained by running the modeled sparse evaluator on those same columns, not by supplying the desired cell values or assuming equality to an honest trace. No decoder success, valid witness, residual correctness, old-residual zero premise, or source-selector equality is assumed. The already-proved `SelectedSelectorExpansion.expanded_row1014_pack_binding` removes the two old residuals using their actual selectors, not an assumed zero value.

The new work establishes the missing lookup interface at this Boolean row. It does **not** establish that proof acceptance enforces the residual at that row, authenticate the supplied tables, establish arbitrary-point source correspondence, or produce a payment witness.

## Source and theorem map

| Pinned source operation | New mathematical model/result | Scope |
|---|---|---|
| `constraints_v4.rs:601–630`: reverse Boolean suffix scan, suffix left shift/OR, prefix range and prefix weights | `sparseWeights`, `trailing_boolean_scan`, `suffix_boolean_decode`, `sparseWeights_boolean` | At every Boolean point the actual modeled output is the singleton `(decoded index, 1)`. The helper's output is not an external hypothesis. |
| `constraints_v4.rs:782–793`: reject non-1024 column, otherwise sum weighted entries | `sourceMle`, `sourceMle_bad_length`, `sourceMle_boolean_checked` | Exact field/list length check and fold. The symbolic index bound makes the totalizing `getD` fallback unreachable for ten Boolean coordinates. |
| MSB-first suffix bit convention | `bitStep_arithmetic`, `decodeFold_bound`, `decodeBits_bound`, `public_bit_inventory` | Generic arithmetic proves the index bound; only the ten public bit values for 1014 and 1015 are concretely reduced. |
| `v6_transcript.rs:529–549`: optimized last-coordinate update, reverse carry loop reading original bits | `sourceSuccessor`, `zero_carry_loop`, `sourceSuccessor_last_zero`, `sourceSuccessor_current` | For any field-valued prefix followed by zero, the modeled successor changes only the last coordinate to one. Specializes to 1014→1015. No general successor result is claimed here. |
| `payment_extraction.rs:26–28`: source `v6_statement_points` then `multilinear_evaluate_qm31` for each message column | `current_mle`, `successor_mle`, `current_point_coordinate` | Current and successor use the same arbitrary supplied table, and the current coordinate vector equals the previously proved selector vector. |
| `positive_transfer.rs:75–84`: current amount, successor amount and current inverse in new residual | `currentPositivePack`, `current_positive_pack_binding` | Exact Boolean-row pack binding after modeled source reads; no change to the existing terminal or challenge factors. |

The array/slice interfaces are represented as lists and field operations. The source's point type has length ten; the total generic list model permits other lengths, but the checked-index theorem explicitly requires ten. The successor model handles an empty list only to totalize its definition; the actual Rust array is nonempty. Actual Rust indexing, integer/memory execution, field-limb implementation and automatic translated-source correspondence remain separate obligations. At the retained Boolean inputs the decoded index is proved below 1024, so the model does not conceal an out-of-range source read behind a default value.

## Reused V7 work

The import chain is `SelectedSelectorExpansion` → `PositivePackBinding` → `PositiveTerminalInsertion` and the cached exact QM31 tower / `V7PairForestCuArithmeticEquivalences` packing identities. It uses the actual tower packing, not an unproved assertion that arbitrary QM31 coefficients form an independent base-field basis.

`V7BooleanZeta` was inspected but not substituted for the current helper: its recursive coordinate convention is low-bit-first, whereas the selected source suffix and row indices here are MSB-first. The new literal loop model avoids silently identifying these conventions. No unchanged V7 theorem was recompiled.

## Evidence and reproduction

Run from the research worktree, with a fresh evidence filename:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_sparse_mle.sh \
  docs/research/v8-no-work-100-20260907/experiments/selected-sparse-mle-v3.log
```

The runner verifies pinned source and olean hashes, recursively checks imported repository modules against the pinned commit and the read-only main cache, and uses the cached Lean 4.32.0 / Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` workspace. It runs only the changed leaf with `lean -M7000` under a process-tree RSS guard at 7,340,032 KiB, with root-serialized jobs. There is no dependency rebuild, SBF build, Rust execution or performance measurement.

`selected-sparse-mle-v1.log` is a retained unsuccessful diagnostic: exit 1, 21.37 seconds, 5,488,934,912-byte peak RSS, zero swaps. Reserved identifier `prefix` caused parse errors, and Option `do` syntax needed an explicit definitional normalization. Its dependent `sorryAx` diagnostics are not evidence of retained proved results. The changed follow-up source renames the local identifiers and normalizes the Option expression; the final successful audit below must contain no `sorryAx`.

The changed-source follow-up `experiments/selected-sparse-mle-v2.log` is green: **exit 0, 12.39 seconds wall time, 5,655,740,416-byte peak RSS, zero swaps**. All 14 `#print axioms` endpoints use only subsets of `propext`, `Classical.choice`, and `Quot.sound`. No new axiom or `sorry` is retained. The runner imported cached dependencies without rebuilding them. Warnings concern unused section instances and one redundant simplifier entry; there were no errors or resource-guard stops.

| Artifact | SHA-256 |
|---|---|
| Final `SelectedSparseMle.lean` | `91f8204107e4caea36f4948f3e27ae270f65413fca01b68ea1ac8ee286fbaaaa` |
| Final `SelectedSparseMle.olean` (local cache artifact) | `5b9379efb68f86aff60f54fe0eb125d0fe17071fe1238318ab887e14f023594c` |
| Imported `SelectedSelectorExpansion.lean` | `3f6c969a075d37f46d2a93c844191dc7dbb9c974c5413bfdf0a73c92ea50999a` |
| Imported `SelectedSelectorExpansion.olean` | `358d9a496a1e56d9b508cf9fa726d8f597e8a6db6626fe05cb982c6236e256cb` |

The remaining imported source/olean pairs and exact compiler command are recorded in the successful log. The source and its compiled artifact were not edited after that check. These are proof-check resources, not proving, extraction or verifier runtime measurements.

## Remaining implication

The checked endpoint still needs recovered canonical semantic columns, source-linked individual point claims, and acceptance-to-exact-constraint enforcement, with all challenge timing and discarded/replay branches charged. This leaf closes only the current/successor sparse-read input to the Boolean positivity pack. It supplies no new probabilistic budget, no extraction runtime bound, no full-view ZK result, and no CU comparison. The next direct composition is to combine this lookup result with the existing positive-output/conservation theorem under the *proved exact semantic residual predicate*, keeping acceptance enforcement and authoritative public context distinct.
