# Differential tests for rewritten functions that had none

Status: target not yet established. This is a test record. Nothing here is a proof. A differential test compares two
bodies on the inputs it tries and says nothing about any other input.

Candidate: commit 4dceeaab48e (branch `aspis-next`, round 2d). Frozen: commit
3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de. The round 2b rewrites (verifier program, with some functions in the core and
statement crates) and the round 2c and 2d rewrites (Pool program) must give the same output and the same error at the
same point as the frozen code. The privacy lead's review listed the functions below as having no differential test,
or only a thin one. This record adds one test module per function.

The work was paused by the owner before the host test run was read; see "Paused" at the end.

## What was changed

Only test code was changed. The ten patches below (`diff -u` against 4dceeaab48e, applied with `patch -p1` from the
repository root) each append new `#[cfg(test)]` modules after the last line of one file. No line of the commit moves or
changes: each of the ten files at the commit is a byte prefix of the file with the tests (checked by script), and no
other file differs. No dependency is added (`sha2`, used by one module, is already a dev-dependency of the verifier
crate). No `unsafe` is used.

| Patch | Modules |
|---|---|
| `aspis-core__state_only_hiding.patch` | `differential_state_only_selected_mask_value` |
| `aspis-statement__state_only_poseidon.patch` | `differential_evaluate_state_only_poseidon_oracle_projected` |
| `aspis-statement__pool_v1_pair_forest_semantic_terminal.patch` | `differential_composition_parts` |
| `aspis-statement__pool_v1_pair_forest_copy_terminal.patch` | `differential_selectors_expand_sizes` |
| `aspis-statement__pool_v1_pair_tree_profile.patch` | `differential_pair_leaf_witness_validate` |
| `aspis-statement__pool_v1_pair_forest_accounts.patch` | `differential_decode_pool_v1_pair_forest_lane_state_v1`, `differential_encode_pool_v1_pair_forest_checkpoint_v1`, `differential_plan_pool_v1_pair_forest_checkpoint_v1`, `differential_checkpoint_lane_sequence_v1` |
| `aspis-r1-cost-probe__candidate.patch` | `differential_wide_view`, `differential_parse_shape` |
| `aspis-r1-cost-probe__one_tx.patch` | `differential_relation_view`, `differential_final_rounds`, `differential_parse_packed_shape` |
| `aspis-r1-cost-probe__weights.patch` | `differential_scalar_factor` |
| `aspis-r1-cost-probe__verifier.patch` | `differential_polynomial_full_range` |

Each module keeps the frozen body as a private function `frozen_<name>`. The adaptations are only the ones its doc
comment names: the new name, `pub` and `#[inline(..)]` dropped, and for `validate` the receiver `&self` written as the
parameter `this`. A token comparison of all fifteen copies against `git show 3d700effcabe:<path>` found every copy
token-identical after those adaptations. The frozen copies call the same shipped helpers as the new bodies. Where such
a helper was itself rewritten, it has its own differential test, named below.

Inputs come from a fixed-seed splitmix64 generator local to each module, so every case count is fixed. Field values
are canonical. Each limb takes one of the edge values 0, 1, 2, p - 2 or p - 1 with probability 3/8, and is otherwise
uniform below p. Parsers and validators also get the non-canonical limbs p, p + 1, 2^31 and 2^32 - 1.

Where the frozen body panics, the test catches the panic of both bodies (`std::panic::catch_unwind`) and requires the
same panic message. Where a function writes through a `&mut` argument, the test also compares the state afterwards,
including after a panic. Only `final_rounds` does so, writing into the transcript. Every comparison covers the
complete result, including the error value.

## Per function

### Round 2b, on the prover's proving path

**`state_only_selected_mask_value`** (`aspis-core`, `state_only_hiding.rs`)
- Changed: the Horner loop `for exponent in (0..26).rev()` became `let mut exponent = 26; while exponent > 0 {
  exponent -= 1; .. }`. It visits the same exponents, 25 down to 0, with the same operations.
- Test: `state_only_hiding::differential_state_only_selected_mask_value::same_result_as_frozen_body`.
- Inputs:
  - 729 cases: every combination of one edge value for all columns, one for all point coordinates and one for the
    explicit mask. The edge values are zero, one, p - 1 in each of the four limbs alone, and all limbs 2, p - 2 or p - 1.
  - 90 cases: one point coordinate at each edge, the others zero.
  - 234 cases: one semantic or mask-only column at each edge, the others zero.
  - 200,000 random cases.
- Cases: 201,053.
- `selected_mask_linears`, which it calls, has its own test (`counted_loop_form`).

**`composition_parts`** (`aspis-statement`, `pool_v1/pair_forest_semantic_terminal.rs`)
- Changed: its two Horner loops over the semantic and Poseidon lanes, `for index in (0..len).rev()`, became counted
  `while` loops over the same indices in the same order. Nothing else changed.
- Test: `pool_v1::pair_forest_semantic_terminal::differential_composition_parts::same_result_as_frozen_body`.
- Inputs:
  - Public statements of both variants, built independently of the frozen transition check so that it accepts them:
    the carry level is free, lower levels and zero-bit levels hold the empty roots, and the rest hold the source
    frontier.
  - Append indices 0, 1, 2, 3, 7, 2^19 - 1, 2^19, 2^20 - 2, 2^20 - 1, and random.
  - Each transition check broken in turn: the pool; the domain; the sequence; the index at 2^20, 2^20 + 1, 2^64 - 2 or
    2^64 - 1; the afterstate index; one frontier level.
  - Withdrawal amounts 0, 1, 2, 2^30 - 2, 2^30 - 1, 2^30, 2^30 + 1 and 2^32 - 1.
  - Claims, point, lambda, chi and theta random, with edge limbs.
- Compared: the six returned values, or the error.
- Cases: 40,182. Of these, 29,250 return values, 2,551 return InvalidPublicAmount and 8,381 return
  InvalidAppendTransition.

**`evaluate_state_only_poseidon_oracle_projected`** (`aspis-statement`, `state_only_poseidon.rs`)
- Changed: `full_low` was `[1, 9, 10].into_iter().fold(..)` and `internal_low` was `(2..=8).fold(..)`. Both became the
  same additions written out from zero, in the same order.
- Test: `state_only_poseidon::differential_evaluate_state_only_poseidon_oracle_projected::same_result_as_frozen_body`.
- Inputs:
  - 81 cases: every pair of edge values, one for all openings and one for all selectors.
  - 144 cases: each local selector row alone at each edge, with random openings.
  - 40,000 random cases: half with the selectors the verifier builds (`at_point` of a random point), half with
    random selectors.
- Cases: 40,225.

### Round 2b, elsewhere

**`wide_view`** (`aspis-r1-cost-probe`, `candidate.rs`)
- Changed: `inactive: E::from_le_bytes(..).ok_or(Error::Parse)?` became an explicit `match` that returns
  `Err(Error::Parse)`. It stays in the same position of the struct literal, so the fields are evaluated in the same
  order.
- Test: `verifier::candidate::differential_wide_view::same_result_as_frozen_body`.
- Inputs:
  - 69 cases at edge proof lengths, each with a canonical inactive field and with limb 0 or limb 7 at p. The lengths are
    0, 1, the inactive offset, that offset + 16 and + 31, and one short, exact and one long at the end of the inactive,
    round-0, folded-root, round-1 and final fields and at the full proof length.
  - 360 cases: full-length proofs with every inactive variant (canonical, or limb 0 or 7 at p, p + 1, 2^31 or
    2^32 - 1), with empty and with non-empty semantic and y1 buffers.
  - 20,000 random proofs, with inactive limbs over the whole range and some non-canonical.
- Compared: every field of the view (slices by address and length), or the error, or the panic message.
- Cases: 20,429. Of these, 11,990 return views and 8,409 return Parse. 30 panic in both bodies with the same message:
  the proof ends before a field that is read before any error.

**`relation_view`** (`aspis-r1-cost-probe`, `one_tx.rs`)
- Changed: `let inactive = E::from_le_bytes(..).ok_or(Error::Parse)?` became an explicit `match`.
- Test: `verifier::candidate::one_tx::differential_relation_view::same_result_as_frozen_body`.
- Inputs:
  - 78 length cases: the `wide_view` lengths plus the one-transaction proof length (55,815) one short, exact and one
    long.
  - 360 cases: full-length proofs of both formats with every inactive variant.
  - 20,000 random proofs of both lengths.
- Cases: 20,438. Of these, 12,009 return views and 8,399 return Parse; 30 panic in both bodies with the same message.

**`final_rounds`** (`aspis-r1-cost-probe`, `one_tx.rs`)
- Changed: in each round, the two `E::from_le_bytes(..).ok_or(Error::Parse)?` (c0, then c2) became explicit `match`es,
  in the same order and before the transcript absorbs the round.
- Test: `verifier::candidate::one_tx::differential_final_rounds::same_result_and_transcript_as_frozen_body`. The
  transcript runs over SHA-256 from the existing dev-dependency and is resumed from a random state.
- Compared: the running claim and the six challenges, or the error. Also the transcript state afterwards, including
  after a panic.
- Inputs:
  - 117 length cases: certificate lengths 0, 1, 768, and one short, exact and one long at the end of every 32-byte
    value.
  - 480 cases: every one of the 96 limbs of a canonical certificate set in turn to p - 1, p, p + 1, 2^31 and 2^32 - 1.
    This gives an error at every round, in c0 and in c2.
  - 9 cases: edge starts (zero, one, all limbs p - 1) on certificates of zeros, of ones and of p - 1.
  - 20,000 random certificates, half of them with one non-canonical limb.
- Cases: 20,606. Of these, 10,121 return Ok and 10,403 return Parse. 82 panic in both bodies with the same message and
  the same transcript state: the certificate ends inside a round that is reached.

**`parse_shape`** (`aspis-r1-cost-probe`, `candidate.rs`)
- Changed: `proof[9..16].iter().any(|&x| x != 0)` became `proof[9..16] != [0u8; 7]`.
- Test: `verifier::candidate::differential_parse_shape::same_result_as_frozen_body`.
- Inputs:
  - 21 cases: lengths 0 to 17, and 57,606, 57,607 and 57,608.
  - 4,096 cases: every value of each of the 16 header bytes, at the exact length.
  - 20,000 random headers.
- Cases: 24,117. Of these, 4,036 return Ok and 20,081 return Parse.

**`parse_packed_shape`** (`aspis-r1-cost-probe`, `one_tx.rs`)
- Changed: the same change as in `parse_shape`.
- Test: `verifier::candidate::one_tx::differential_parse_packed_shape::same_result_as_frozen_body`.
- Inputs:
  - 22 cases: lengths 0 to 17, and 55,814, 55,815, 55,816 and 57,607.
  - 4,096 cases: every value of each header byte.
  - 20,000 random headers.
- Cases: 24,118. Of these, 4,042 return Ok and 20,076 return Parse.

**`Weights::scalar_factor`** (`aspis-r1-cost-probe`, `weights.rs`)
- Changed: `(0..4).fold(E::ZERO, ..)` became a counted `while` loop. It adds the same four terms in the same order,
  then applies the same multiplication by one quarter.
- Test: `weights::differential_scalar_factor::same_result_as_frozen_body`.
- Inputs:
  - 48 cases: each of the four positions of both arrays at an edge, with the others random. The factor edges are zero,
    one and all limbs p - 1; the value edges are zero, one, all limbs p - 1 and all limbs p - 2.
  - 12 cases: all four positions at one edge pair.
  - 200,000 random cases.
- Cases: 200,060.

**`factored_s2_libra_weights`** (`aspis-r1-cost-probe`, `weights.rs`)
- Changed: the local binder `weights` was renamed `libra_w`. Nothing else changed.
- Token comparison: each body has 464 tokens, and 8 positions differ, all of them the binder (`weights` in the frozen
  body, `libra_w` in the new one). Neither body uses the other name anywhere.
- No test was written, because a test would add nothing.

### Pool rounds 2c and 2d

**`PoolV1PairLeafWitnessV1::validate`** (`aspis-statement`, `pool_v1/pair_tree_profile.rs`)
- Changed: `second_commitment.iter().any(|limb| one_minus_occupied.mul(*limb) != M31::ZERO)` became the eight products
  written out, left to right, joined by `||`. The products have no side effects.
- Test: `pool_v1::pair_tree_profile::differential_pair_leaf_witness_validate::same_result_as_frozen_body`.
- Inputs:
  - 6,520 cases: valid occupied and empty witnesses, with each commitment limb, the occupancy and the inverse set in
    turn to 0, 1, 2, p - 2, p - 1, p, p + 1, 2^31 and 2^32 - 1.
  - 16 cases: empty witnesses with one non-zero commitment lane, with a zero and with a non-zero inverse.
  - 300,000 random cases, unstructured and structured near the valid sets.
- Cases: 306,536. Outcomes: Ok 117,403, NonCanonicalCommitment 76,194, NonCanonicalOccupancy 487, NonCanonicalInverse
  404, OccupancyNotBoolean 804, SentinelInverseMismatch 58,826, EmptyInverseNonZero 16,545, EmptyCommitmentNonZero
  35,873.
- Not reached: `OccupiedSentinelZero`, because an occupancy of one has already required sentinel × inverse = 1; and
  `SelectedSlotEmpty`, which `validate` does not return.

**Lane-state decoder `decode_pool_v1_pair_forest_lane_state_v1`** (`aspis-statement`, `pool_v1/pair_forest_accounts.rs`)
- Changed: `bytes[73..80].iter().any(|byte| *byte != 0)` became `any_nonzero_byte(&bytes[73..80])`, the crate's index
  loop.
- Test: `pool_v1::pair_forest_accounts::differential_decode_pool_v1_pair_forest_lane_state_v1::same_result_as_frozen_body`.
- Inputs:
  - Six valid lane images: trees with 0, 1, 2, 3 and 5 appended leaves and a full tree at index 2^20; lane ids 0 to 5;
    bumps 0, 255 and random.
  - For each image:
    - every value of every header byte, 0 to 79 (magic, version, lane id, lane count, depth, format binding, master,
      bump, reserved bytes);
    - six values (0, 1, 0x7f, 0x80, 0xff, and the byte with its low bit flipped) at every tree byte;
    - every length from 0 to 776, which includes one byte short, exact and one byte long.
  - 20,000 random images with several fields changed at once.
- Cases: 172,316. Outcomes: Ok 53,204, WrongLength 4,656, WrongMagic 6,153, WrongVersion 1,542, WrongLaneCount 1,540,
  WrongDepth 1,541, WrongFormatBinding 49,298, NonZeroReserved 15,450, ZeroRequiredBinding 6,534, InvalidLane 2,849,
  tree errors 29,549.
- Not reached: the decoder's own `InvalidMasterState` (tree index above 2^20), because the tree decoder rejects such an
  index first.
- Both bodies call the shipped `decode_with_empty_roots`, which has its own test in `incremental_merkle.rs`.

**Checkpoint encoder `encode_pool_v1_pair_forest_checkpoint_v1`**
- Changed: the capacity check `lane_sequences.iter().any(..)` became `any_lane_sequence_above_capacity(..)`. The copy
  loop over `iter().enumerate()` became an index `while` loop that writes the same eight sequences to the same offsets.
- Test: `pool_v1::pair_forest_accounts::differential_encode_pool_v1_pair_forest_checkpoint_v1::same_result_as_frozen_body`.
- Compared: the complete 192-byte output, or the error.
- Inputs:
  - 13,650 cases from 50 valid checkpoints:
    - each lane sequence at 0, 1, 2^20 - 1, 2^20, 2^20 + 1, 2^64 - 2 and 2^64 - 1;
    - each root limb at 0, 1, 2, p - 2, p - 1, p, p + 1, 2^31 and 2^32 - 1;
    - the bump and the checkpoint sequence at their edges;
    - the master and the domain all zero, and with one non-zero byte at each position.
  - 300,000 random cases, where several errors at once are possible.
- Cases: 313,650. Outcomes: Ok 118,830, ZeroRequiredBinding 39,545, InvalidMasterState 87,953, NonCanonicalDigest
  67,322.

**Checkpoint planner `plan_pool_v1_pair_forest_checkpoint_v1`, as a whole**
- Changed:
  - The per-lane loop, with returns inside it, became eight calls of `checkpoint_lane_sequence_v1` (lanes 0 to 7
    written out, the first error returned).
  - The progress loop became `checkpoint_lane_progress_v1`. It returns 0 for progressed, 1 for decreased and 2 for no
    progress, mapped to the same two errors as before.
  - `checked_add(1).ok_or(..)?` became an explicit `match`.
- Test: `pool_v1::pair_forest_accounts::differential_plan_pool_v1_pair_forest_checkpoint_v1::same_result_as_frozen_body`.
- Compared: the complete plan (next master and checkpoint), or the error.
- Inputs: 300,000 cases.
  - Valid masters: mutable and immutable policies; with and without a checkpoint; next checkpoint sequence 1, 2,
    2^64 - 2, 2^64 - 1 or random.
  - Lanes whose sequences are small or at the capacity edge, with last sequences equal, one below or one above.
  - Four cases in five get one to three mutations at once, each breaking a different check, so that several lanes and
    several checks fail in one input and the first failing one decides. The mutations are:
    - a zero pool or domain;
    - the policy flags;
    - a last sequence above the capacity;
    - an inconsistent checkpoint flag;
    - an incomplete lane mask;
    - a non-canonical root limb;
    - a lane's master changed;
    - two lanes swapped;
    - a wrong lane id (8, 255, or the next lane's);
    - a lane index above the capacity;
    - next checkpoint sequence 2^64 - 1, 2^64 - 2 or 0.
- Outcomes: Ok 23,624, ZeroRequiredBinding 71,439, InvalidMasterState 84,404, LaneMasterMismatch 11,137,
  LaneOrderMismatch 22,244, LaneSequenceDecreased 35,238, DuplicateCheckpoint 3,823, CheckpointSequenceOverflow 2,371,
  NonCanonicalDigest 16,148, Policy 29,572. These are all the errors the frozen planner returns.
- Both bodies call the shipped `validate_master`, which has its own test (`translatability_oracle`).

**`checkpoint_lane_sequence_v1`** (new in round 2c)
- Changed: this function is new. Its body is the three checks of one iteration of the frozen planner loop.
- Test: `pool_v1::pair_forest_accounts::differential_checkpoint_lane_sequence_v1::same_result_as_frozen_loop_iteration`.
- Compared against: that loop iteration (frozen lines 490-501), with the three checks verbatim, the pool key passed as
  a parameter, and the stored value returned.
- Inputs:
  - 55,296 cases: every lane id 0 to 255, × expected lane 0 to 8, 255, 256 or `usize::MAX`, × index 0, 1, 2^20 - 1,
    2^20, 2^20 + 1 or 2^64 - 1, × master equal, one bit different, or zero.
  - 100,000 random cases.
- Cases: 155,296. Outcomes: Ok 3,423, LaneMasterMismatch 61,790, LaneOrderMismatch 89,068, InvalidMasterState 1,015.

### Thin coverage extended

**`polynomial`** (`aspis-r1-cost-probe`, `verifier.rs`, round 2b)
- Changed: `(0..7).rev().fold(..)` became a counted `while` loop over the same indices, 6 down to 0.
- Gap closed: the existing test draws only the low four limbs of each 32-byte value, so every high half is zero.
- Test: `verifier::differential_polynomial_full_range::same_result_as_frozen_body_over_the_whole_range`. It draws all
  eight limbs of every coefficient and of the point.
- Inputs:
  - 25 cases: every coefficient and the point at zero, one, all limbs p - 1, all limbs p - 2, or p - 1 in the first
    high limb only.
  - 8 cases: byte lengths 0, 1, 32, 192 and 223 (these panic in both bodies), and 224, 225 and 256.
  - 28 cases: one non-canonical limb (p or 2^32 - 1) at limb 0, 3, 4 or 7 of each coefficient. These panic in both
    bodies with the same message.
  - 200,000 random cases.
- Cases: 200,061. Of these, 200,028 return values and 33 panic in both bodies with the same message.

**`Selectors::expand`** (`aspis-statement`, `pool_v1/pair_forest_copy_terminal.rs`, round 2b)
- Changed: the inner loop `for index in (0..len).rev()` became a counted `while` loop with the same writes in the same
  order.
- Sizes used:
  - The function is private to its file. Its only caller, `Selectors::at_point`, calls it with N = 64 (six coordinates,
    `high`) and N = 16 (four coordinates, `low`).
  - No other size occurs in the crates. The `expand` functions in `state_only_poseidon.rs`, `state_only_terminal.rs`
    and other files are separate functions and were not rewritten.
  - The existing test covers N = 16 only.
- Test: `pool_v1::pair_forest_copy_terminal::differential_selectors_expand_sizes::same_result_as_frozen_body_at_sizes_16_and_64`.
- Inputs:
  - 108 cases: every coordinate count, 0 to 6 at N = 64 and 0 to 4 at N = 16, with all coordinates at each edge value.
  - 108 cases: one coordinate at each edge, the others random.
  - 40,000 cases: `at_point` against the frozen body on both halves of 20,000 random points.
  - 240,000 cases: 20,000 random coordinate lists, at every count.
  - 20 cases: one coordinate too many at both sizes (7 at N = 64, 5 at N = 16). Both bodies panic with the same
    index-out-of-bounds message.
- Cases: 280,236.

## Local results

These runs are on the development machine (macOS 27.2, arm64, rustc 1.93.0 stable, `cargo test --release --offline`)
in a copy of 4dceeaab48e plus the ten patches. The resulting file set is identical to the host test tree (`find crates
programs tools -type f | sort | xargs sha256sum | sha256sum`: 10dd43730c29437d9b55239beb7c00a4cc32eb3523db08a31fe6e5c6efcc48ba
on both machines).

All 17 new tests pass and none fails:

| Crate and features | New tests | Indicative wall time per test |
|---|---|---|
| `aspis-r1-cost-probe --features 'prover aspis' --lib` | 7 of 7 passed | wide_view 574 ms, relation_view 581 ms, final_rounds 171 ms, parse_shape 55 ms, parse_packed_shape 55 ms, scalar_factor 85 ms, polynomial 157 ms |
| `aspis-statement --features r0,pool-v1-kernel --lib` (one thread) | 8 of 8 passed | Poseidon oracle 385 ms, composition_parts 1,265 ms, expand 138 ms, validate 46 ms, lane decoder 1,194 ms, encoder 37 ms, planner 2,165 ms, lane sequence 183 ms |
| `aspis-core --lib` | 1 of 1 passed | 368 ms |

The full lib suites pass in the same configurations: verifier crate 69 passed, 0 failed; core 287 passed, 0 failed,
2 ignored; statement 295 passed, 0 failed. No warning points into the appended code.

These are local runs with a different toolchain from the gate's (1.94.1). They are not the host record.

## ELF result

The build host ran job `X8-builds-1` (one `fv_slot.sh` scope, MemoryHigh 6G, MemoryMax 8G, no swap). It used the
lead's recipes `fv_frz_build.sh` (verifier, features `aspis`, Pool id 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt,
registry id 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q) and `fv_pool_build.sh` (Pool, deployed feature list), with
cargo-build-sbf 3.1.13, platform-tools v1.52 and rustc 1.89.0. The job exited 0 in 6:10.75 wall time, with a cgroup
peak of 2,002,010,112 B and no memory events.

The build trees, both made with `fv_frz_tree.sh` from the archive of 4dceeaab48e (archive sha256
ec976ec063949743a980bc24341c6cc75cafa6aca8a57260c7bcab85883218d0), were:
- `src-x8-1`, the plain commit;
- `src-x8-2`, the commit plus the ten patches.

| Program | `src-x8-1` (without the tests) | `src-x8-2` (with the tests) |
|---|---|---|
| verifier | 33d66a28424051e56a2d33dadc5f29c717abbc5ff81e6023ada1987dd9d628ea (955,280 bytes) | 33d66a28424051e56a2d33dadc5f29c717abbc5ff81e6023ada1987dd9d628ea (955,280 bytes) |
| Pool | 6302e3550929733736a07d035084438eb5dbf3397d856bb3a20613a938f7a83a (321,240 bytes) | 6302e3550929733736a07d035084438eb5dbf3397d856bb3a20613a938f7a83a (321,240 bytes) |

Both programs are byte-identical with and without the tests.

## Paused

The owner paused all Aspis work while the host test run was in progress. That run is job `X8-tests-1`, started at
2026-11-12 19:33 UTC in one `fv_slot.sh` scope (slot 3) under nohup. It runs the gate's test steps 1, 1b, 2, 3 and 3b
from `fv_round_checks.sh` on `W/x8/tree` with toolchain 1.94.1, and then the new tests alone with their case counts and
wall times, in both the deployed and the client configuration.

It was started and has not been read. It was neither stopped nor checked after the pause.

Read it next (`W = ~/project-offloads/future-version-20261111`):
- the exit status and summary line in `W/x8/X8-tests-1.slot.log`;
- the receipt in `W/receipts/X8-tests-1/` (exit, time.log, cgroup_memory_peak, memory_events);
- the per-step results in `W/x8/runs/X8-tests-1/steps.txt`, with the logs beside it.

The steps file ends with `status: PASSED` or `status: FAILED`. The program-test steps (step 3) exit 101 by design in
the deployed configuration, because of the 25 two-transaction tests that fail under one-transaction settings. Compare
their outcome lists (`program-tests-*.outcomes`) with the frozen gate's.

If a new test fails on the host, that is a finding: the rewrite differs from the frozen code. Report it with its input
and both outputs; do not change the test or the function.

The host scripts are `W/x8/bin/fv_x8_tests.sh` (sha256 820acb9080377dac7b391e126a86a72902c91e97a75caa4d57fe081f69d14c4c),
`W/x8/bin/fv_x8_builds.sh` (sha256 4a2dcc9802adb69aa0c770286e20b721208dad517e714c29cf2e4635ecbbbabe) and
`W/x8/bin/verbatim_check.py` (sha256 0dc641f6948984e5d331d8dabf66e9b6093168f92dadc8997b75e6dff8db3d65). The patches
are in `W/x8/patches/`.

## Not covered

- Host test results: unread at the time of the pause (above).
- The frozen copies call the shipped helpers, not frozen copies of them. Each test compares one rewritten body, and
  the rewritten helpers rely on their own differential tests.
- `OccupiedSentinelZero` (in `validate`) and the lane decoder's own `InvalidMasterState` are not reached by any input
  tried. The reasons are given above.
