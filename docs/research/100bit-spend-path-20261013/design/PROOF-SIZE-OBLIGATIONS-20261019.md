# Proof-size candidate: proof obligations inventory (2026-10-19)

Measurement 6 of `PREREG-PROOF-SIZE-20261019.md`. Candidate: compact QM31
storage plus binary C1/C2/folded trees with one multiproof per tree per
transaction batch (10/12), fixed-length 57,607-byte stored proof
(`evidence/proof-size-20261019/REPORT.md`, feature `compact-binary`).
Read-only source inventory at base 20e596416; nothing here is proved. Paths:
`lean/` = `docs/research/100bit-spend-path-20261013/lean/`, `R1Z/` =
`docs/research/v8-r0-zk-20261009/lean/R1Z/`. Row ids in brackets are the
R1 soundness gap map's (`R1-SOUNDNESS-GAP-MAP-20261019.md`, branch
`codex/r1-soundness-gapmap-20261019`).

Sizes as in the gap map: S = one focused module or check; M = a
multi-module bridge over existing extraction; L = new extraction plus
multi-module proof, or a whole-cone audit.

## 0. What does not change

- The relation, the 33 transcript rows and their message byte strings: the
  candidate rebuilds every semantic record and `y1` in its logical 32-byte
  form before hashing (`compact::expand_*`), so `LiteralTranscript`,
  `RawChecksInjectionFormat.checks_imply_injection_format` and the row
  formats keep their statements. What changes in the transcript is only the
  *values* of the three roots (binary-tree roots), hence of every challenge
  after the C1-time binding.
- Leaf grammar `0x10 || tag || value || salt` (`lean/Merkle32Leaf.lean`
  `leafInput`, `lean/MerkleLeafCodec.lean`), salts, the fold/accumulate/
  relation code, `finish_relation`, checkpoint format.
- Parameters (22 queries, two folds, final length 64, WideExact values).
- The algebraic binding and classifier modules (M2-M5, `ConcreteBinding`,
  `LiteralClassifier`, `PerAttemptEnvelope`): they read challenges, not tree
  shapes.

## 1. Commitment binding (soundness)

| Module / declaration | Today | Change | Size |
|---|---|---|---|
| `lean/Merkle32Path.lean` `nodeInput`, `nodeInput_length` (= 257), `nodeBytes_injective`, `Children := Fin 8 -> Digest` | eight-way node `0x18 || 8 children` | add a binary node `0x12 || l || r` (65 bytes) with its injectivity and length lemmas, or generalise over arity | S |
| `lean/MerkleNodeCodec.lean` `parse`, `parse_nodeInput`; `lean/MerkleNodeRecordUnique.lean` `nodes_unique_by_digest`; `lean/MerkleTable.lean` `lookup`, `lookup_mem`, `lookup_exists` | 257-byte node parser, 8-child table | binary parser and table | S |
| `lean/MerkleIndexGeometry.lean` `slots`, `index`, `index_slots` (`List (Fin 8)`, depth 6) | 6 slots of 8 | 18 slots of 2 (`index_slots` at `i < 2^18`) | S |
| `lean/Merkle32Leaf.lean` `leaf_path_binding`, `fullTrace`, `FullTraceCollision`; `lean/MerkleProgram.lean` `pathProgram_accepts_iff`, `leafProgram_accepts_iff`; `lean/CanonicalMerkleProgram.lean` `reads_canonical`, `fullTrace_bounded` | path binding over `List (Fin 8)` | the same statements over binary paths of length 18 | M (mechanical, whole small cone) |
| Collision targets: `lean/RawByteCollisionTargets.lean` (eleven targets: eight strict child parsers, two root readers, duplex state), `lean/MerkleChildTargets.lean` `pred`, `mass`, `lean/CombinedMerkleTargets.lean` `pred` (`Fin 10`), `lean/CombinedMerkleCollision.lean` `budget = 12 Q^2/2^256`, `lean/RawAdaptiveDecoderInjection.lean` `kappa` | 8 child targets | 2 child targets (left/right of a 65-byte node); the union bound's constant changes (fewer targets), every downstream use of `kappa` / `budget` re-instantiated | M |
| Domain separation of the new tag `0x12` from leaves (`0x10`), eight-way nodes (`0x18`), duplex frames and every other hashed message under the same oracle | n/a | new disjointness lemma at the byte level (first byte / length) | S |

## 2. Multiproof verification

New, no counterpart today.

| Obligation | Rust | Size |
|---|---|---|
| Indexed multiproof soundness: for strictly increasing indices, `verify_in_place` accepting implies every leaf's literal 18-step binary path is in the oracle log and ends at the root (the multiproof analogue of `MerkleWalkWitness.walk_witness` and `lean-candidates/current-merkle-path-20261019/RawMerkleAcceptedWalk.accepted_walk`, `RawMerkleAcceptedLiteralPath.accepted_literal_path`), with exact node consumption (`at == nodes.len()`), single top at index 0 | `multiproof::verify_in_place`, `well_formed`, `node_count` | M (model) |
| Source refinement of the batch: sort by u64 keys, merge equal folded indices only with identical leaves, reject otherwise; slot geometry (`compact::slot_offset`, `SLOT_NODES`), zero padding, node count from the transcript queries; batch A in stage 1, batch B in stage 2 | `candidate::batch_merkle`, `multiproof::node_count` | L (new Aeneas extraction of the candidate cone and its proof) |
| The counting bound used for the fixed length (`MAX_NODES = 914`): `node_count <= SLOT_NODES[s]` for every query set | REPORT section 1 argument; `multiproof` unit tests | S |
| Replaces the open gap-map row [R13] (eight-way actual Merkle verification), whose candidate files (`RawMerkleParentCall`, `RawMerkleParentBytes`, `RawMerklePathWalk`, `RawMerkleStepWitness`) model the eight-way `merkle_path` and would be discarded | `verifier::merkle_path` no longer on the candidate route | (R13 was M) |

## 3. Extractor commitment-word recovery

The extractor walks the recorded oracle log from each root through eight-way
node records. Every module below is parameterised by eight-way paths and
would be restated for binary paths (the walk length 6 becomes 18).

| Module / declaration | Size |
|---|---|
| `lean/MerkleRecovery.lean` `walk_reconstruct`, `recover_or_bad`; `lean/RecoveredRootRecorded.lean` `walk_root_recorded`, `recover_root_recorded`, `canonical_root_read`; `lean/RecordedRecoveryWitness.lean` `recover_witness`; `lean/MerkleLogExtension.lean` `walk_append`, `recover_append` | M |
| `lean/ThreeCommitmentRecovery.lean` and `lean/ThreeCommitmentFullTrace.lean` `c1_recover_of_no_events`, `c2_recover_of_no_events`, `folded_recover_of_no_events`; `lean/CanonicalC1Recovery.lean` `recover_or_events`; `lean/CanonicalTypedOpening.lean` `paths6C1C2`, `paths6Folded` (`slots 6`), `c1/c2/folded_decode_of_no_events`, `folded_word_of_no_events` | M |
| Merkle compiler [M7]: `lean/RawCompiledRunWordStabilityV8.lean` `wordsFromRun_compiled_eq_original`, `wordsFromRun_compiled_eq_retainedBuildWords`; `lean/RawChecksAdaptiveCleanModel.lean` `clean_model_of_checked_acceptance_no_hit`; then the composed bound [M9] `lean/RawChecksAdaptiveFailureNoModel.lean` `checked_acceptance_failure_bound_no_model` re-checked | M |
| Source commitment words [R11, R12]: `lean/RawSourceC2WordBinding.lean` `actual_c2_word_stable`, `actual_c2_opening_projects_word`; `lean/RawSourceC2CutBinding.lean`; `lean/RawCutOpeningWordProjection.lean` `actual_raw_cut_openings_project_literal_word` (the opening projection reads the multiproof instead of per-query paths) | M |
| Extractor cost [M10]: `lean/MerkleRecoveryCost.lean` `walkCount_cost`, `lookupCount_cost` (18 lookups per path instead of 6; the bound stays polynomial) | S |

## 4. Root, transcript and proof serialization

| Obligation | Module / Rust | Size |
|---|---|---|
| Compact representation refinement: the strict compact parse plus rebuild yields exactly the logical semantic prefix and `y1` the shipped parser accepts, and the candidate accepts a stored proof iff the shipped checks accept its logical image (strict decoding, complete consumption, implied-zero halves) | `compact::{expand_semantic, expand_values, check_values}`, `candidate::{parse_shape, canonical_scan, prepare, wide_view}`; re-uses `lean/ActualDecodeKStrictQM31Parser.lean` `source_refines` [R5], `lean/ExtractedRecordValidator.lean`, `lean/ExtractedRecordStrictCodec.lean`; the shipped `echeck(y1, true)` becomes a 16-byte canonical scan (`compact::check_values`), while the wide scans (`lean/CanonicalLiteralEcheckSevenChunks.lean` for the 7-value round messages) are unchanged | M |
| Proof layout in the reachability statements: `lean/ExtractedPreparedReachability.lean` `prepare_success`, `output` (built from `verifier::View`; the candidate builds the `View` from rebuilt buffers) [R4, R6] | `candidate::prepare` | M |
| Roots in the transcript: C1 root in the C1-time binding, C2 root in row 2, folded root in row 30 keep their byte positions; only the tree that produces them changes. `lean/LiteralTranscript.lean` `c1At` etc. unchanged; the source-side root derivation is part of section 3 | none new | S |
| Checkpoint over the compact stored bytes [R15]: `resume` hashes the stored 57,607 bytes; stage 2 trusts batch-A padding through that hash | `verifier::{checkpoint, resume}` (unchanged code, new input) | S |

## 5. Oracle-read counts in the soundness and privacy error terms

Soundness (first-read budget `Q`, [R19]):

- `lean/VerifierCallBudget.lean` `queryBudget = 3 + 3*6` per query,
  `stage1Budget 10 = 328`, `stage2CoreBudget = 465`, `verifierBudget = 472`
  (all `rfl`). With batch multiproofs the per-batch count is `3k` leaves plus
  at most `3*(14k + 15)` binary parents for `k <= 16` (465 parents at k = 10,
  549 at k = 12, against 180 and 216 eight-way parents). On the same
  counting conventions: stage 1 = 82 + 33 + 30 + 465 + 3 = 613; a stage 2
  that, as today's constant, counts all 22 queries = 3 + (30 + 465) + (36 +
  549) = 1,083 (plus 7 PDA reads). New constants, the `SourceCountObligation`
  instance, and every use of `Q` in `RawAdaptiveMembershipBound.membership_bound`
  (`hQ`) and `kappa Q` re-instantiated. The resulting change of `kappa Q =
  12 Q^2/2^256` is negligible, but the theorems name the constants. Size S
  (constants) on top of the open M work of [R19].

Privacy (commitment-read count, LOG D41 read budget):

- `R1Z/CommitReadsR1.lean` `CRead` (eight-way nodes `Sigma d : Fin 6,
  Fin (8^(5-d))`), `card_nodes = 37449`, `McR1 = 1,685,214 + E1 + E2`,
  `card_CRead`, and `mc_le : 115 + McR1 (2 L1) (2 L2) <= 2^21`.
  A binary tree has 2^18 - 1 = 262,143 nodes, so Mc becomes 1,572,864 +
  786,429 + 3 = 2,359,296 + E1 + E2, and with the source counts
  (`RCommitCount`: E1 + E2 <= 2(44*1024) + 2(4*1024) = 98,304) `115 + Mc`
  reaches 2,457,715 > 2^21 = 2,097,152. **`mc_le` is false for the
  candidate.** The D41 read budget must rise (2^22 suffices), and every
  privacy error term stated with the 2^21 budget is re-derived. Size M,
  plus a lead decision on the budget.
- `R1Z/TranscriptR1.lean` (115 transcript reads, `card_TRead`) is
  unchanged: the transcript reads are the same messages.

## 6. Privacy simulator and commitment layout

| Module / declaration | Today | Change | Size |
|---|---|---|---|
| `R1Z/GamesR1P.lean` `NodeIdx := Sigma d : Fin 5, Fin (8^(5-d))`, `RIdx`, `CPos`, `realGameP`, `fsR1P` | 8-ary non-root nodes | binary node index (17 non-root levels) | M |
| `R1Z/LayoutR1P.lean` `nodeBytes` (8 children), `child_bound0`, `child_bound`, `fld_gram`, `nodeBytes_update`; `R1Z/LayoutR1P2.lean` `qNode_inj`, `childQ_cases`, `childQ_ne_bind`, `childQ_ne_seed` (`Fin 8` children); `R1Z/LayoutR1P3.lean` `rd_rootChild`, `rd_childQ`, `rd_salt`, `rd_seed` | 8-ary index algebra and readers | binary index algebra | M |
| `R1Z/EventsR1P.lean` `ROpen` ("the verifier opens exactly the roots and the paths of the opened fibres"), `RComLog`; `R1Z/EventsR1P3.lean` `hit_tr`, `hit_cm`, `pair_all` | opened set = union of eight-way paths | opened set = the multiproof's supplied nodes plus the computed ancestors (the union of binary paths), with the deterministic zero padding as public bytes | M |
| `R1Z/PrivacyR1P.lean` `privacy_R1_games'`, `idealModelS_R1P` (premise `RCommitBytes` names the 8-ary node grammar) | | re-stated over the binary layout and the new Mc (section 5) | M |
| Rust simulator `crates/aspis-r1-cost-probe/src/sim.rs` `program_tree` (programs leaf and node reads on the union of opened eight-way paths and emits shipped-layout paths) and the R1 simulator gate | eight-way, shipped layout | binary programming, candidate stored layout (compact fields, slots, padding) | M |

## 7. Source re-pins and release gates

- New Rust cone, all unextracted: `verifier::candidate::{parse_shape,
  canonical_scan, wide_view, prepare, batch_merkle, query_values, tx1,
  tx2_common, tx2_authenticated, tx2}`, `multiproof::{verify_in_place,
  node_count, well_formed, sort_dedup}`, `compact::{expand_semantic,
  expand_values, check_values}`, the adapter shim (`r1_pool_adapter.rs`
  `mod verifier`) and the `lib.rs` line-47 selection. The shipped
  `query_with_geometry` Merkle part is replaced; `query_values`,
  `QueryGeometry`, `BatchedWeights`, `accumulate_with_node`, `finish_relation`
  are reused unchanged. Whole-cone declaration inventory and extraction:
  L ([S10], [R14], [R16] are re-targeted, not added to).
- The pre-registered worst-case CU bound (`PREREG-CU-UPPER-BOUND-2-20261019.md`)
  re-run on the candidate before any 1.3M claim: M (compute-bound).
- Prover: `host_commitment::Commitment` (binary tree), `prover::
  prove_candidate_from_semantics`; the r1p retry path (`public_check`) is
  wired but was not exercised by the measurement driver. S.

## 8. Summary

Top obligations, by size:

1. **L** Source refinement of the candidate verifier cone (section 7) with
   the batch multiproof (section 2, second row).
2. **M, with a decision** Privacy read budget: `mc_le` (`R1Z/CommitReadsR1.lean`)
   fails for binary trees (2,457,715 > 2^21); raise the D41 budget and
   re-derive the privacy error terms (section 5).
3. **M** Binary commitment binding and collision targets
   (`Merkle32Path`, `RawByteCollisionTargets`, `CombinedMerkleCollision`,
   `RawAdaptiveDecoderInjection.kappa`; section 1).
4. **M** Extractor word recovery and the Merkle compiler over binary paths
   (`MerkleRecovery`, `ThreeCommitmentRecovery/FullTrace`,
   `CanonicalTypedOpening`, `RawCompiledRunWordStabilityV8`,
   `RawChecksAdaptiveCleanModel`, `RawSourceC2WordBinding`; section 3).
5. **M** Privacy commitment layout (`GamesR1P`, `LayoutR1P*`, `EventsR1P*`,
   `PrivacyR1P`) and the Rust simulator (section 6).
6. **M** Compact representation refinement (section 4) and multiproof model
   soundness (section 2, first row).
7. **S** Read-count constants (`VerifierCallBudget`), the `0x12` domain
   separation lemma, the extractor cost lemma, checkpoint-over-compact.

None of these is started. The compact-only part (section 4, first row) is
independent of the tree change and is the smallest self-contained piece.
