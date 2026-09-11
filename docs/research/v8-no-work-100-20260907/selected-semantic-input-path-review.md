# Selected same-table historical input path — unverified follow-up

Status: **source draft only; no Lean run or axioms result**. The stop-batch instruction is to preserve this follow-up without compiling or changing the NUC cache. The existing green Afterstate V2 closeout is separate. This report does not promote the eleven pending `#print axioms` declarations to checked results.

Source parent: `125320408ae38060fab9c97391958025d353ce10`.
Draft: [SelectedSemanticInputPath.lean](experiments/SelectedSemanticInputPath.lean), SHA256 `662cb8261202e55374a398d0bb10f9262039f7ede6c2c41d2222aa9ce03f2d3b`.

## The genuine remaining bridge

`SelectedSemanticTransferV2.transfer_facts` already derives strict positive amounts/conservation, the owner hash, input-note hash and public nullifier from the same key/salt, input-pair parser/spendability, and output notes. It does **not** connect the selected input-pair commitment to this input note and the full historical forest root. Repeating its owner or nullifier equations would not close that gap.

The new draft constructs every field of `SelectedForestPath.PathResiduals` from the existing complete `RowsVanish`, `PoseidonChecks`, and `WeightedAliases` on `semanticTable candidate`. It then reuses `SelectedMembershipDecode.same_decoded_note_nullifier_and_anchor`. The target conclusion is:

- the actual decoded pair's selected commitment is the note hash of this table's owner/key, amount, public asset and salt;
- the public nullifier is the nullifier hash of the same key and salt;
- the actual decoded one-pair/twenty-lane/three-forest path computes the public anchor.

No correct-root, decoder-success, honest-trace, valid-witness, acceptance, or caller-authentication premise replaces the individual residuals.

## Exact selected layout

For `0 ≤ l < 24`, write `a(l)=913+16⌊l/4⌋+4(l mod 4)`, `b(l)=4+l` for `l≤20` and `33+l` otherwise, and `d(0)=59`, `d(l)=16b(l−1)+11` for positive `l`.

| Actual link | Producer → consumer | Tuple pattern | Supplied path field |
|---|---|---|---|
| `64+3l` | row `d(l)` low8 → row `a(l)` columns1–8 | 1 → 12 | current copy |
| `65+3l` | row `a(l)+1` low8 → row `16b(l)+12` low8 | 1 → 1 | left copy |
| `66+3l` | row `a(l)+1` high8 → row `16b(l)` high8 | 13 → 10 | right copy, subtracting the literal last-limb node tweak |

All72 weights are the actual constant `.one`, not append-selected weights. This gives576 scalar aliases from144 endpoint occurrences. Pattern10 adds `1051521018 = −1095962629` in M31; the existing symbolic `literal_right_offset_cancels` proves the cancellation. Equality in QM31 is established **before** projection to `.re.re`; no multiplicative projection of an arbitrary extension-field value is assumed.

| `PathResiduals` prerequisite | Draft source projection |
|---|---|
| 24 Boolean directions | position32 at `a(l)`, whose actual path selector is one |
| selected left/right | positions33–40 / 41–48 at the same `a(l)` |
| current/left/right copy | the72 literal links above |
| node initial low zeros | initial positions0–7 at `16b(l)`; first-block and occupancy summands are separately inactive |
| all24×11 round-pair equations | `PoseidonChecks` at block `b(l)` and proved equality of both `pairState` definitions, including rate8 absorption |
| public historical root | digest positions84–91 at row907; all append siblings, root859, bounded carry row, nullifier and output terms are isolated, not deleted |

The transition between lane and forest is explicit: level20 uses block24; level21 uses block54. The boundary rows are59 initially,395 after the pair plus twenty lane levels, and907 after all24 levels. No old20-level Tag73 path or old one-output registry is substituted.

## Existing proof reuse and cache boundary

- `SelectedForestPath.decoded_ordered_children` reuses pinned V7 `gated_selected_child_forces_ordered_children`; `roundChainOfResiduals` constructs the missing intermediate Poseidon states; `complete_selected_path` closes the exact24-step fold.
- `SelectedEarlyC1Outputs.rawSemanticTable`, `raw_canonical`, and `rawTable_exact` construct canonical raw representatives and recover the same field table everywhere. No parser-canonicality premise is added.
- `SelectedEarlyC1Inputs.input_residuals_from_selected_copy` and `SelectedSemanticTransfer.note_checks` derive `NoteResiduals`, rather than supplying an already-correct input note.
- `SelectedMembershipDecode.same_decoded_note_nullifier_and_anchor` is the existing final consumer. Its companion `same_raw_input_pair_checked` and `decoded_lane_index_contract` remain available; the new endpoint itself is not advertised as a full checked-payment witness.

Direct draft imports are `SelectedSemanticAfterstateChecksV2` (to reuse `sibling_sum_at_eleven`) and `SelectedMembershipDecode`. The latter is absent from the inspected1061-entry afterstate per-run manifest. Its local prior green source/output pair exists, but no copy or registration was performed:

| Artifact | SHA256 |
|---|---|
| `SelectedMembershipDecode.lean` | `cc91edd69fdbfb023b16ba443e7cfc0b6657cd272565a82a10ed2546a5addad2` |
| local `SelectedMembershipDecode.olean` | `30d16ee5b6add0867901de13e8a4bdc49c2007de7a3fe60682559dd57305a6f2` |
| `SelectedForestPath.lean` | `8f0248edf14e711cc50f5038c3968ae5e90fc9b6ba01aba2e5ad94a8ece8e409` |
| V7 `V7PairForestGatedMerkle.lean` | `f1e40eac2a8971119e827777e0581292a11467a30f6529a08c2cebdbe08e687a` |
| `HashMerkleModel.lean` | `114b0140eeb440e538493e424456bf08f67ef4bcf0935b9c17fc503c174a588a` |

The retained `selected-membership-decode-v3.log` records Lean4.32 on macOS and fourteen standard-only audits. This is existing evidence, **not** a new NUC compatibility or import-closure verification. Before any future run, the coordinator must verify compatible exact imported artifacts and authorize any no-overwrite append or focused missing dependency check. No cold build is authorized by this report.

## Bounded static falsification check

A read-only Python regex comparison against the current Rust constants checked all136 Lean/Rust endpoint triples, then every72 path-link tag/kind/level/endpoint tuple, four participating pattern expansions, all24 path masks/node-block ranges, and the literal tweak sum. It returned:

```json
{"status":"PASS_STATIC_ONLY","whole_registry_links":136,"path_links":72,"path_endpoint_occurrences":144,"path_limb_aliases":576,"path_levels":24,"path_patterns_checked":[1,10,12,13]}
```

The exact checked source is `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs`, SHA256 `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50`. The existing `audit_component_cover_evidence.py:layout_metadata` independently retains the full136-link/14-pattern correspondence. The additional24-level formulas above were directly compared with every triple; no field enumeration, Rust execution, formal theorem check, or probability experiment occurred. `git diff --check` is only whitespace validation.

## Remaining obligations — not discharged by this draft

The table candidate is fixed throughout, but the theorem neither proves it is an `EarlyC1Family` member nor recovers it from an accepted transcript. `RowsVanish`, the same-table mathematical Poseidon equations and the copy-alias branch still need their established causal/source premises. The copy collision alternative, all four denominator poles, helper totals and inactive-slot obligations remain upstream; weight-one projection does not remove them.

The `pub.anchor` digest is not thereby an independently authenticated retained checkpoint. Rust/PDA/CPI/account projection, asset and lane authority, checkpoint retention, nullifier non-spentness and settlement authorization remain external. Neither collision resistance nor knowledge of a private key follows just from evaluating the modeled owner hash. The existing modeled decoder/path proofs are not a universal proof of the deployed Poseidon implementation or round constants.

The smallest useful future check is this one new leaf, after cache preflight and serial authorization. Only its72 small metadata lookups use scoped depth1000 (the existing selected-layout convention); field, path and decoder applications remain depth200. All eleven audits are pending. There is no wall-time/RSS/swap/result claim for this draft.
