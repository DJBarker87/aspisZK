# Append and afterstate reuse inventory

Read-only source inventory. Snapshot: repository `/Users/dominic/ZK/.worktrees/100bit-spend-path`, branch `codex/100bit-spend-path-20261013`, revision `65d5de037cf0acae9b15545ef88d9d5bb6800e0a`. This note distinguishes the two Rust evaluation routes and the generic Lean append model. It does not establish that the current R0P proof is wired to the current Rust gate.

## What public prevalidation checks

`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs` defines `PoolV1PairLiveSnapshotV1` and `PoolV1PairLatePublicStatementV1` at lines 396–411. `validate_pool_v1_pair_live_snapshot_v1` (private; called from codec functions) lines 443–463 checks nonzero pool/domain, `sequence == next_pair_index`, `next_pair_index < capacity`, and canonical field encodings of `current_root` and each frontier digest. The comparisons of sequence/index/capacity are integer comparisons; canonicality is a per-limb `M31` encoding check. This validator does not prove that `current_root` is the reconstruction of `frontier`.

`encode_pool_v1_pair_late_public_statement_v1` lines 529–540 and `decode_pool_v1_pair_late_public_statement_boxed_v1` lines 621–631 check the integer condition `source.next_pair_index.checked_add(1) == candidate.next_pair_index`, with byte framing and decoding. They do not verify candidate root/frontier recurrence. The statement/result codec checks canonical digest encodings and binding equality, not the append hash chain.

`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs` has enum variants `PrivateTransfer` and `Withdrawal` at lines 105–115 and a byte `transition_kind` parser at 190–200 that admits only those two variants. `validate_pool_v1_pair_forest_terminal_statement_v1` lines 227–275 dispatches to the corresponding payment validator, then checks pool/master and deployment bindings, anchor/checkpoint sequence equality, historical anchor equality, nullifier-derived output lane, and encodes the late transition. Payment public validators are in `payment_relation.rs`: `validate_pool_v1_private_transfer_public_v1` lines 220–230 validates common canonical fields and both commitments; `validate_pool_v1_withdrawal_public_v1` lines 232–246 additionally rejects amount 0 or `>= VALUE_LIMIT`, zero destination, and noncanonical change commitment.

## Evaluator route A: current semantic terminal / R0P callback

`crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` has two distinct entrypoint families.

- The macro at lines 1348–1422 generates the private-transfer and withdrawal composition, unmasked-terminal, and masked-terminal evaluators (names at 1425–1439). All call `composition_parts` or `terminal_parts`; `terminal_parts` calls `composition_parts` (1302–1309), which checks public withdrawal amount and calls `validate_transition` (1216–1240).
- `validate_transition` lines 180–209 uses integer arithmetic for `source.sequence == source.next_pair_index`, capacity, checked `index + 1`, and `carry = min(index.trailing_ones(), 20)`. For each frontier level it checks empty/source values based on the old index bit, but skips the carry level. It does not read or compare `candidate_afterstate.next_root` and does not constrain a carry node’s hash. It is a host-side shape/metadata guard, not the append hash recurrence.
- The explicit variant conversions are `private_public` / `withdrawal_public` at 1312–1345; `initial_variant_selectors` branches at 218–239. `r0::Public` has `Transfer` and `Withdrawal` variants at 1978–1988. `Public::terminal_qm31` at 2044–2063 selects the first 28 lanes per point and calls `terminal_parts`. This runs the `validate_transition` precheck **and** the Poseidon, packed semantic, and copy evaluations in `composition_parts` (1253–1278). It does not call either legacy constraint-residual evaluator. Absence of that call is not evidence that the current proof lacks append constraints: the current schedule, digest, and copy gates must be composed and audited separately.
- The active callback caller is `crates/aspis-prover/src/state_only_candidate_prefix.rs`: `build_with_helper` states that its sumcheck oracle is `Public::terminal_qm31` at 762–775; the sumcheck closure calls it at 874–889. `crates/aspis-prover/src/r0.rs` imports `build_pair_forest_transported` and this R0 `Public` at lines 3 and 16–20. No direct or transitive call from these paths to `pair_forest_constraint_residuals` or `pair_constraint_residuals` was found in the source call graph.

A test at `pair_forest_semantic_terminal.rs` lines 1938–1965 mutates `candidate_afterstate.next_frontier[0][0]` and expects `InvalidAppendTransition`; it exercises the precheck only. It is not evidence of a checked candidate root recurrence.

## Evaluator route B: inactive host residual validation

This is a separate entrypoint and does call the residual evaluators.

- `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::verify_pool_v1_pair_forest_terminal_inactive_v1` (host-only) validates account/live-snapshot bindings at 736–747, chooses a residual evaluator by enum variant at 748–776, then checks residual count and `all_zero()` at 778–797.
- The selected public wrappers are `pair_forest_constraint_residuals.rs::evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1` (412–455) and `...withdrawal...` (457–490). They project to legacy coordinates, call the corresponding evaluator in `pair_constraint_residuals.rs`, then `assemble` forest-specific residuals.
- `pair_constraint_residuals.rs::evaluate_append_result_residuals` lines 616–648 constructs append-path, candidate-root, candidate-frontier, and index-sequence residuals. `append_append_path_bindings` lines 570–593 requires each trace append node’s ordered children to equal the current trace digest and the source frontier/empty sibling chosen by the source index bit. `candidate_frontier_expected` lines 595–614 and root/frontier residual construction 616–648 tie the candidate frontier to carry outputs and the candidate root to terminal `trace_digest(trace, 53)`. These are `M31` field residuals, ultimately checked for zero by the inactive host validator; the source-index bit/carry selection is computed from integer indices. This route is not reached by the R0 `terminal_qm31` callback above.

## Lean model coverage and gap

`AspisFormal/AspisFormal/Pool/V7PairAppendAfterstateCorrect.lean` gives a generic model. `ExactPairAppendTransition` lines 54–75 requires a valid pair leaf, source index/frontier/root invariant, exact `appendCarry` output frontier, incremented sequence/index, and result root reconstructed from that frontier. Named results: `candidateResult_exact` (91–116), `exact_transition_result_root_correct` (120–136), `exact_transition_indices` (140–152), and `payload_reconstructs_exact_result` (158–173). `Pool/IncrementalMerkleV1.lean` provides `FrontierInvariant.root_correct` (666–702), `FrontierInvariant.append_preserves` (706–730), and `append_correct` (735–744).

The pool settlement models consume this relation as an explicit proof premise: `V7EightLaneForestTerminal.lean::ForestTerminalAccepted.appendExact` at 83–84; `V7PairForestLaneInvariant.lean::accepted_terminal_preserves_forest_lane_invariant` at 158–189 uses it. `V7PairAppendAfterstateCorrect.exact_transition_result_root_correct` proves root correctness given that exact relation. These are abstract models; they do not by themselves show that the current R0 Rust terminal’s `terminal_qm31` callback enforces that relation.

The model’s source boundary is explicit: `IncrementalMerkleV1.lean` lines 825–833 defines `PoseidonV3SourceRefinement` and says the Rust/Aeneas bridge must establish production `merkle_node_compress_v3` and the all-zero M31 digest equal the abstract parent/empty leaf. No direct R0P theorem importing or constructing `ExactPairAppendTransition` from the current R0 semantic terminal/gate callback was found in the current Lean source set. Existing R0P semantic theorems therefore do not close this evaluator wiring by inspection alone.

## Pinned source hashes

| Path | SHA-256 |
|---|---|
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` | `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074` |
| `crates/aspis-prover/src/state_only_candidate_prefix.rs` | `a04147941fc2f8e0c9667caf9dc7f1f4e0bd8ce8add740bbe6bee88c2c3e05b5` |
| `crates/aspis-prover/src/r0.rs` | `6fc60f3e24799f0d6473c016410f0abc371f9084004814af5182ac412ae4ef8b` |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs` | `becc01f162f23cd9b4a7fd3780be5a441c9b7265f3078282244cc938da63a16c` |
| `crates/aspis-statement/src/pool_v1/pair_forest_constraint_residuals.rs` | `7bafd96ef01b1013fe587777860d4be3b48acd3043c87ce618a28c2cc02638f8` |
| `crates/aspis-statement/src/pool_v1/pair_constraint_residuals.rs` | `c59a9033e814781b90f67c2dd6d91ddc3b7d4a0ea4a5af9a11f8be70db990e95` |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs` | `8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2` |
| `AspisFormal/AspisFormal/Pool/V7PairAppendAfterstateCorrect.lean` | `ab7aa39d4c1e341f4188f1001b3e3ca67915ee75517fc55422bf0c51dc147a83` |
| `AspisFormal/AspisFormal/Pool/IncrementalMerkleV1.lean` | `930aa1fb6aee6bbcba746b37397253d9f96bdf9d2fd96e6cfe3102da80e4f0dc` |
| `AspisFormal/AspisFormal/Pool/V7PairForestLaneInvariant.lean` | `9bac4ad614af759e46ab0fea2a348f88430ed056e2249cc3de67c8b0b955eea0` |
| `AspisFormal/AspisFormal/Pool/V7EightLaneForestTerminal.lean` | `745eb77b3a15f0abd816c7f95e1bba34e70df264fb63e7c9f6490f0d4f111b00` |
## Later checked checkpoint

The literal production append path is now connected in
[APPEND-GATE-BRIDGE.md](APPEND-GATE-BRIDGE.md): output-pair occupancy,
twenty nodes, next root, and carry frontier binding, with an explicit
non-carry public-check premise for the full frontier. This does not yet
establish `ExactPairAppendTransition`. The frozen-table recurrence and
the `.full` capacity branch require the separate bridge described in
[APPEND-TABLE-BOUNDARY.md](APPEND-TABLE-BOUNDARY.md).
