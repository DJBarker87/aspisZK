# J1 source reuse: current pair-forest input path

Inspection pin: HEAD `57edab99fe104f23b3d3c881d1e87c1abb0975c0`. This note records source definitions and existing Lean interfaces only.

## Keep the path profiles distinct

There are three nearby but different interfaces in this checkout:

1. `PoolV1MembershipWitnessV1` in `crates/aspis-statement/src/pool_v1/payment_relation.rs` is the legacy single-note depth-20 witness (`siblings: [Digest; POOL_V1_TREE_DEPTH]`, `index: u32`). Its `evaluate_pool_v1_*` functions are not the current pair-forest input-path implementation.
2. The pair-tree builder in `pair_trace.rs` represents an input pair leaf, a private selected-side bit, and 20 upper pair-tree siblings. `pair_forest_trace.rs` adds three super-root siblings/bits, so its complete private direction vector is 24 bits. This geometry matches the abstract 24-step path arity in the current R0P Lean input-witness relation, but this inventory does not assert a Rust-to-Lean equality.
3. `InputWitnessCore.Relation` in Lean quantifies `path : Fin 24 → Bool × Digest`; its first path sibling is explicitly the other commitment in the pair leaf. Its later path steps are represented abstractly by `merkleRoot`. Do not read the legacy Rust depth-20 public-payment evaluator as this 24-step relation.

## Current pair-forest Rust witness and preparation

- `PoolV1PairInputNoteWitnessV1` (`pair_trace.rs:69-79`) carries `nullifier_key: Digest`, `salt: Digest`, `value: u32`, `pair_leaf: PoolV1PairLeafWitnessV1`, `selected_second: bool`, and `membership: PoolV1MembershipWitnessV1`. The latter's 20 siblings/index are the upper pair-tree path; source comment says the pair leaf supplies the private bottom direction.
- `PoolV1PairLeafWitnessV1` (`pair_tree_profile.rs:90-102`) contains `first_commitment`, `second_occupied`, `second_commitment`, `second_occupancy_inverse`. Validation (`:115-150`) requires canonical digest limbs and occupancy/inverse in M31; `second_occupied` Boolean; sentinel-times-inverse equals occupancy; inverse is zero for empty; every second digest limb is zero when empty; and an occupied second slot has nonzero sentinel. `require_selected_spendable` (`:174-183`) rejects selecting the second slot unless occupancy equals one. The first slot is the always-present slot in the format binding (`:42-75`). `leaf_digest` is the ordered compression of first and second commitments (`:153-163`).
- For the pair-tree path, `lane_root` starts at the pair leaf digest and hashes 20 indexed siblings (`pair_forest_trace.rs:91-105`). `relocate_and_extend` (`:197-242`) copies the legacy path's 21 directions (selected-side plus 20 index bits), adds 3 `super_root_directions`/`super_root_siblings`, hashes blocks 54–56, and checks the result against the expected global anchor. The forest input wrapper (`:51-58`) contains the pair witness plus `[Digest; 3]` super-root siblings and `[bool; 3]` directions. The vector length 24 and the three-level extension are also named constants in `pair_forest_hiding.rs:36-46`; path hash blocks select `4+level` for levels 0–20 and `33+level` for levels 21–23 (`:77-85`).
- The current forest preparation entry points are `compile_pool_v1_pair_forest_private_transfer_merged_c1_v1` and `compile_pool_v1_pair_forest_withdrawal_merged_c1_v1` (`pair_forest_trace.rs:316-379`). Each builds the legacy pair trace under the lane root, extends it to the global anchor, merges the C1 banks, and returns `PoolV1PairForestMergedC1CompilationV1`. The higher semantic preparation path accepts this compilation in `pair_forest_semantic_terminal.rs`; the public wrapper's `build` additionally checks the compiled semantic C1 width and equality of `compiled.public_statement` with `public.transition()` before invoking semantic construction (see `crates/aspis-r1-cost-probe/src/host_semantic.rs` and `crates/aspis-r1-cost-probe/src/semantic.rs` in the active cost-probe surface).

## Domains, note fields, values, and variants

- `crates/aspis-statement/src/spend.rs:14-21` defines `DOMAIN_OWNER_KEY = 0x41530001`, `DOMAIN_NULLIFIER = 0x41530002`, `DOMAIN_NOTE = 0x41530003` (and the separate Merkle-node domain). `derive_owner_key` hashes the nullifier key under owner-key domain (`:121-134`). `derive_nullifier` hashes key concatenated with salt under nullifier domain (`:125-143`). `note_commitment` hashes 18 fields under note domain: owner-key digest (8 M31 fields), value, asset id, salt digest (8 fields), in that order (`:146-166`).
- Pair-trace helpers mirror these preimages (`pair_trace.rs:227-252,510-557`): derive owner from input nullifier key; hash input note `(owner,value,asset,salt)`; validate selected commitment; build pair and 20 upper path; hash nullifier key then salt. In the pair-forest wrapper, the extended anchor adds the final three super-root levels (`pair_forest_trace.rs:197-242`).
- `validate_common` in current pair trace checks runtime pool/domain/sequence/root/asset bindings, no spent nullifier, canonical key/salt/path digests, `0 < input.value < VALUE_LIMIT`, upper index `< 2^20`, and selected slot spendability (`pair_trace.rs:470-508`). `VALUE_LIMIT` is `2^30` (`spend.rs:10`). Transfer preparation additionally enforces `0 < recipient.value, change.value < 2^30` and checked sum equal to input value (`pair_trace.rs:600-627`). Withdrawal preparation enforces `0 < change.value < 2^30` and checked `amount + change.value = input.value` (`:703-727`); its public amount validator separately requires `0 < amount < 2^30` (`payment_relation.rs:232-246`).
- The public Rust enum is `PoolV1PairForestTerminalStatementV1::{PrivateTransfer,Withdrawal}` (`pair_forest_terminal.rs:90-140`). `SemanticPublic` conversion is exact: transfer sets `recipient=Some(recipient_commitment)` and `withdrawal_amount=None`; withdrawal sets `recipient=None` and `withdrawal_amount=Some(amount)` (`pair_forest_semantic_terminal.rs:1312-1345`). Its SPEC §9 semantic byte serialization emits variant 0/1, anchor, nullifier, asset, recipient option tag and payload if present, change, withdrawal option tag and payload if present, then append-state fields (`:1996-2040`).

## Existing Lean reuse

- `AspisR1.InputWitnessCore.Relation` (`lean/InputWitnessCore.lean:13-22`) states valid pair, selected slot spendable, selected commitment equal to `noteCommitment (ownerKey sk) value pub.assetId salt`, sibling at path index 0 equals the unselected pair commitment, nullifier equals `nullifierHash sk salt`, and anchor equals `merkleRoot` of that note commitment over the 24-step path. `pair_head` (`:51-59`) derives that the first Merkle step is the ordered compression of the exact pair commitments.
- `InputPairSelection.Facts` and `of_production` (`lean/InputPairSelection.lean:58-70`) package pair validity, pair compression, selected-output equality and selected spendability from production/copy-link hypotheses. `InputWitness.of_production` (`lean/InputWitness.lean:13-23`) composes that with the trace-provided key/salt/nullifier/membership fact; `bounded_of_production` (`:26-41`) additionally gets natural value bounds/conservation from `SpendValues.of_value_balance`.
- `SpendSemantics.NoteFacts` (`lean/SpendSemantics.lean:11-25`) includes bounded balance, `InputNoteExtracted`, change commitment, and conditional recipient/withdrawal-output facts. It explicitly omits public option-shape parsing and Rust correspondence. `R1InputWitness`/`InputPairSelection` therefore supply semantic witness facts, not the J1 byte-level statement parser.

## Source pins

- `crates/aspis-statement/src/pool_v1/pair_trace.rs`: `80290c5af3e8102da8e43efbadccfde745af272c2bfb046a919d5ce4da9f9371`
- `crates/aspis-statement/src/pool_v1/pair_forest_trace.rs`: `0a97cbba7740acf44e3b85082ff917e6fb60b81a26662a2d7f96acaf0e72309d`
- `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs`: `61bcd59a22c9c02fe3f9ba69cda43bfa8fe02ea14f15da9b761e976fe48798bf`
- `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs`: `8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2`
- `crates/aspis-statement/src/spend.rs`: `1cee5f45331207c1841106838daea76126f85b1c97b1066bc39089a6cb623ee9`
- `crates/aspis-statement/src/pool_v1/format.rs`: `209bf45ab1fbf03fa6a5b524e6b2079068537368b02837e320d708ca5128f88d`
- `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`: `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074`
- `lean/InputWitnessCore.lean`: `fec688b4ae7650f4ba4c266613853eb9f858aabd5d36f2d8a5f4d01107a85d5d`
- `lean/InputWitness.lean`: `a4462b34d5d50f8195938c5e786dbf88a79a9d3b2b68b241c7fd43571554530e`
- `lean/InputPair.lean`: `e97853456b75cc9970db0504df22b398802cc81d03993d492eec59f2d348316e`
- `lean/InputPairSelection.lean`: `7c0aa7bc71afe9d6b2e4ff8c59847dad28f76529d7d5682ac8f8d1c479400f45`
