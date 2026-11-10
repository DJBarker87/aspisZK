# PCVY_ transcription review (op50, decode_lane_from_pool_release)

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, programs/r1-cost-probe/src/r1_pool_adapter.rs lines 448-520 (read with `git show`),
against evidence/prov-p3t-20261110/PCVV_LaneDecodeRef.lean (byte-identical copy compiled as module PCVV_LaneDecodeRef in scope PCVY_L002, exit 0).
This is a reading check by one reviewer, not a proof. Label of the transcription is unchanged: REVIEWED_TRANSCRIPTION_PENDING_OWNER.

## Result
No line is transcribed differently. No corrected copy PCVY_LaneDecodeRef.lean was written; the equality work below targets the P3t file unchanged.

## Line-by-line (Rust line -> Lean), all agree
- 452-464 length guard and 8 header guards: same eight disjuncts in the same order; `usize::from(bytes[5]) >= COUNT` -> `(at' bytes 5).toNat >= laneCount`; `COUNT as u8` -> `UInt8.ofNat`; `bytes[73..HEADER].iter().any(!=0)` -> `(sl bytes 73 headerBytes).any (· != 0)`.
- 465-470 master = bytes[40..72] (try_into cannot fail on a 32-byte slice), zero test: agree.
- 471-479 tree = bytes[80..] and the five tree guards: agree (`tree[5] != DEPTH as u8`, `tree[6]` hash version, `tree[7]` digest encoding version).
- 480-487 next_leaf_index = u64::from_le_bytes(tree[8..16]); `> POOL_V1_PAIR_CAPACITY`: agree (`le` is little-endian foldr; capacity bound is strict `>`).
- 488-493 root = decode_digest_canonical(tree[16..48]): agree.
- 494-506 frontier loop: level 0..DEPTH, start = 48 + 32 level, decode, then `(nli >> level) & 1 == 0 && node != EMPTY[level]` -> early Err. Rust precedence (`&` binds tighter than `==`) and Lean precedence (`&&&` 60, `==` 50) give the same parse; `frontierLoop` with fuel = DEPTH and `node :: rest` preserves order.
- 507-509 `nli == 0 && root != EMPTY[DEPTH]`: agree (index 20 of a 21-entry table).
- 510-519 result record: bump = bytes[72], lane_id = bytes[5]: agree.
- All Rust error values are the single `InvalidAccountData`, collapsed to `none`: agree.
- Out-of-range indexing would panic in Rust; every slice is in range once the 768-byte guard holds (80 + 48 + 20 * 32 = 768), and `||` short-circuits. The transcription's total `sl`/`at'` therefore agree on the guarded domain; this is the one place the model is total where Rust is partial, and the guard makes it unreachable.

## Constants (struct K) against the frozen text (instantiated as PCVY_Op50.K0 in PRVEq_Op50_p9.lean)
- POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES = 768 (pair_forest_accounts.rs:31, `assert == 768` at :92); HEADER_BYTES 80; LANE_MAGIC `ASL8`; LANE_VERSION 2; LANE_COUNT 8.
- POOL_V1_PAIR_TREE_DEPTH = POOL_V1_TREE_DEPTH = 20 (format.rs:28, pair_tree_profile.rs:33, assert at :363); POOL_V1_PAIR_CAPACITY = 1u64 << 20 = 1048576.
- POOL_V1_TREE_STATE_MAGIC `ASPT`, VERSION 1 (incremental_merkle.rs:24-25); POOL_V1_TREE_HASH_VERSION 3; POOL_V1_DIGEST_ENCODING_VERSION 1 (format.rs:25-27).
- POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING: `ASPISFOREST8`, MASTER_VERSION 2, LANE_VERSION 2, CHECKPOINT_VERSION 2, LANE_COUNT 8, DIGEST_ENCODING 1, DEPTH 20, 1, 13 zero bytes = the 32 bytes in K0 and in NCV_Reference.BINDING.
- V7_PAIR_EMPTY_ROOTS (programs/aspis-verifier/src/v7_pair_empty_roots.rs, `#[path]`-included at r1_pool_adapter.rs:49): 21 digests; all 168 words equal NCV_Reference.EMPTY (PCVY_check_consts.py, output PCVY_CONSTS_CHECK.json, roots_equal true). K0.emptyRoots reads NCV_Reference.EMPTY, so this script is the link between K0 and the frozen table.
- decode_digest_canonical (atomic_statement.rs:91-111) = eight `M31::from_le_bytes`; M31::from_le_bytes returns None iff the u32 >= P, P = 0x7fff_ffff = 2147483647 (field.rs:19, :239-247). PCVY_Op50.decDig (PRVEq_Op50_p8.lean) is that definition; NCV_Reference.digest uses the same bound (`x >= 2147483647`).

## Not covered by this review
Rust semantics of `try_into` and slice indexing are taken as stated above, not formalised. The equality deployed op50 = transcription is only partly proved (see PCVY_HANDOFF.md).
