-- PCVV_LaneDecodeRef.lean: REVIEWED_TRANSCRIPTION_PENDING_OWNER
-- Hand transcription of programs/r1-cost-probe/src/r1_pool_adapter.rs lines 448-520 at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387
-- (fn decode_lane_from_pool_release), in the form of NPL_PublicBytesRef: every Rust line is quoted next to its transcription.
-- It is NOT an Aeneas emission (Aeneas fails on this function: "Early returns inside of loops are not supported yet",
-- see PCVV_CANNOT_EXTRACT.json). Proposed trust row: ReviewedTranscription-LaneDecode (owner decision pending).
-- Conventions: every `return Err(ProgramError::InvalidAccountData)` is `none` (the function has this one error value);
-- `Ok(Box::new(..))` is `some`. `Box::new` is erased. Slice ranges are in bounds once the line-452 length guard holds (Rust would
-- panic otherwise; the guard precedes every indexing, and `||` short-circuits). `.try_into()` of a slice whose length is
-- exactly the array length is always Ok, hence the `.map_err(..)?` on lines 465-467, 480-483, 488-492, 497-501 never fires.
-- Constants and the two external callees are parameters (struct K) bound to the frozen crate items named in each field.
-- Nothing is proved about this file except that it compiles; the equality deployed op50 = decodeLane is NOT proved.
namespace PCVV_LaneDecodeRef

structure K (Dig : Type) where
  /-- POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES (crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs:31) -/
  accountBytes : Nat
  /-- POOL_V1_PAIR_FOREST_LANE_MAGIC = *b"ASL8" (pair_forest_accounts.rs:28) -/
  laneMagic : List UInt8
  /-- POOL_V1_PAIR_FOREST_LANE_VERSION -/
  laneVersion : UInt8
  /-- POOL_V1_PAIR_FOREST_LANE_COUNT -/
  laneCount : Nat
  /-- POOL_V1_PAIR_TREE_DEPTH (pair_tree_profile.rs:33) -/
  treeDepth : Nat
  /-- POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING -/
  accountFormatBinding : List UInt8
  /-- POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES = 80 (pair_forest_accounts.rs:30) -/
  headerBytes : Nat
  /-- POOL_V1_TREE_STATE_MAGIC = *b"ASPT" (incremental_merkle.rs:24) -/
  treeStateMagic : List UInt8
  /-- POOL_V1_TREE_STATE_VERSION -/
  treeStateVersion : UInt8
  /-- POOL_V1_TREE_HASH_VERSION -/
  treeHashVersion : UInt8
  /-- POOL_V1_DIGEST_ENCODING_VERSION -/
  digestEncodingVersion : UInt8
  /-- POOL_V1_PAIR_CAPACITY = 1u64 << POOL_V1_PAIR_TREE_DEPTH (pair_tree_profile.rs:35) -/
  pairCapacity : Nat
  /-- V7_PAIR_EMPTY_ROOTS[i] -/
  emptyRoots : Nat -> Dig
  /-- aspis_statement::decode_digest_canonical on a 32-byte slice: `none` is its Err -/
  decodeDigest : List UInt8 -> Option Dig

structure Lane (Dig : Type) where
  bump : UInt8
  master : List UInt8
  laneId : UInt8
  nextLeafIndex : Nat
  root : Dig
  frontier : List Dig

/-- `bytes[a..b]` -/
def sl (bytes : List UInt8) (a b : Nat) : List UInt8 := (bytes.drop a).take (b - a)
/-- `bytes[i]` -/
def at' (bytes : List UInt8) (i : Nat) : UInt8 := bytes.getD i 0
/-- u64::from_le_bytes on 8 bytes -/
def le (l : List UInt8) : Nat := l.foldr (fun b acc => b.toNat + 256 * acc) 0

variable {Dig : Type} [DecidableEq Dig]

/-- Lines 495-506, the `for (level, node) in frontier.iter_mut().enumerate()` loop with its early return (504). -/
def frontierLoop (k : K Dig) (tree : List UInt8) (nli : Nat) : Nat -> Nat -> Option (List Dig)
  | 0, _ => some []
  | fuel + 1, level =>
    -- L496:     let start = 48 + 32 * level;
    let start := 48 + 32 * level
    -- L497-L502: *node = decode_digest_canonical(tree[start..start + 32].try_into().map_err(..)?).map_err(|_| InvalidAccountData)?;
    match k.decodeDigest (sl tree start (start + 32)) with
    | none => none
    | some node =>
      -- L503:         if (next_leaf_index >> level) & 1 == 0 && *node != V7_PAIR_EMPTY_ROOTS[level] {
      -- L504:             return Err(ProgramError::InvalidAccountData);
      if (nli >>> level) &&& 1 == 0 && node != k.emptyRoots level then none
      else
        match frontierLoop k tree nli fuel (level + 1) with
        | none => none
        | some rest => some (node :: rest)

def decodeLane (k : K Dig) (bytes : List UInt8) : Option (Lane Dig) :=

  -- L448-L450 fn decode_lane_from_pool_release(bytes: &[u8]) -> Result<Box<PoolV1PairForestLaneStateV1>, ProgramError>
  -- L451 use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;  (k.emptyRoots)

-- L452:     if bytes.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES
-- L453:         || bytes[..4] != POOL_V1_PAIR_FOREST_LANE_MAGIC
-- L454:         || bytes[4] != POOL_V1_PAIR_FOREST_LANE_VERSION
-- L455:         || usize::from(bytes[5]) >= POOL_V1_PAIR_FOREST_LANE_COUNT
-- L456:         || bytes[6] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8
-- L457:         || bytes[7] != POOL_V1_PAIR_TREE_DEPTH as u8
-- L458:         || bytes[8..40] != POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING
-- L459:         || bytes[73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES]
-- L460:             .iter()
-- L461:             .any(|byte| *byte != 0)
-- L462:     {
-- L463:         return Err(ProgramError::InvalidAccountData);
-- L464:     }
  if bytes.length != k.accountBytes
      || sl bytes 0 4 != k.laneMagic
      || at' bytes 4 != k.laneVersion
      || (at' bytes 5).toNat >= k.laneCount
      || at' bytes 6 != UInt8.ofNat k.laneCount
      || at' bytes 7 != UInt8.ofNat k.treeDepth
      || sl bytes 8 40 != k.accountFormatBinding
      || (sl bytes 73 k.headerBytes).any (fun byte => byte != 0) then none else

-- L465:     let master: [u8; 32] = bytes[40..72]
-- L466:         .try_into()
-- L467:         .map_err(|_| ProgramError::InvalidAccountData)?;
-- L468:     if master == [0u8; 32] {
-- L469:         return Err(ProgramError::InvalidAccountData);
-- L470:     }
  -- L465-L467 let master: [u8; 32] = bytes[40..72].try_into().map_err(..)?;   (Ok: the slice has exactly 32 bytes)
  let master := sl bytes 40 72
  -- L468 if master == [0u8; 32]
  if master == List.replicate 32 0 then none else

-- L471:     let tree = &bytes[POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES..];
-- L472:     if tree[..4] != POOL_V1_TREE_STATE_MAGIC
-- L473:         || tree[4] != POOL_V1_TREE_STATE_VERSION
-- L474:         || tree[5] != POOL_V1_PAIR_TREE_DEPTH as u8
-- L475:         || tree[6] != POOL_V1_TREE_HASH_VERSION
-- L476:         || tree[7] != POOL_V1_DIGEST_ENCODING_VERSION
-- L477:     {
-- L478:         return Err(ProgramError::InvalidAccountData);
-- L479:     }
  -- L471 let tree = &bytes[POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES..];
  let tree := bytes.drop k.headerBytes
  if sl tree 0 4 != k.treeStateMagic
      || at' tree 4 != k.treeStateVersion
      || at' tree 5 != UInt8.ofNat k.treeDepth
      || at' tree 6 != k.treeHashVersion
      || at' tree 7 != k.digestEncodingVersion then none else

-- L480:     let next_leaf_index = u64::from_le_bytes(
-- L481:         tree[8..16]
-- L482:             .try_into()
-- L483:             .map_err(|_| ProgramError::InvalidAccountData)?,
-- L484:     );
-- L485:     if next_leaf_index > POOL_V1_PAIR_CAPACITY {
-- L486:         return Err(ProgramError::InvalidAccountData);
-- L487:     }
  -- L480-L484 let next_leaf_index = u64::from_le_bytes(tree[8..16].try_into().map_err(..)?);
  let nli := le (sl tree 8 16)
  -- L485 if next_leaf_index > POOL_V1_PAIR_CAPACITY
  if nli > k.pairCapacity then none else

-- L488:     let root = decode_digest_canonical(
-- L489:         tree[16..48]
-- L490:             .try_into()
-- L491:             .map_err(|_| ProgramError::InvalidAccountData)?,
-- L492:     )
-- L493:     .map_err(|_| ProgramError::InvalidAccountData)?;
  match k.decodeDigest (sl tree 16 48) with
  | none => none
  | some root =>

-- L494:     let mut frontier = [[M31::ZERO; 8]; POOL_V1_PAIR_TREE_DEPTH];
-- L495:     for (level, node) in frontier.iter_mut().enumerate() {
-- L496:         let start = 48 + 32 * level;
-- L497:         *node = decode_digest_canonical(
-- L498:             tree[start..start + 32]
-- L499:                 .try_into()
-- L500:                 .map_err(|_| ProgramError::InvalidAccountData)?,
-- L501:         )
-- L502:         .map_err(|_| ProgramError::InvalidAccountData)?;
-- L503:         if (next_leaf_index >> level) & 1 == 0 && *node != V7_PAIR_EMPTY_ROOTS[level] {
-- L504:             return Err(ProgramError::InvalidAccountData);
-- L505:         }
-- L506:     }
  -- (L494 `let mut frontier = [[M31::ZERO; 8]; DEPTH]` is overwritten element by element by the loop)
  match frontierLoop k tree nli k.treeDepth 0 with
  | none => none
  | some frontier =>

-- L507:     if next_leaf_index == 0 && root != V7_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH] {
-- L508:         return Err(ProgramError::InvalidAccountData);
-- L509:     }
  if nli == 0 && root != k.emptyRoots k.treeDepth then none else

-- L510:     Ok(Box::new(PoolV1PairForestLaneStateV1 {
-- L511:         bump: bytes[72],
-- L512:         master,
-- L513:         lane_id: bytes[5],
-- L514:         tree: IncrementalMerkleTreeV1 {
-- L515:             next_leaf_index,
-- L516:             root,
-- L517:             frontier,
-- L518:         },
-- L519:     }))
-- L520: }
  some { bump := at' bytes 72, master := master, laneId := at' bytes 5, nextLeafIndex := nli, root := root, frontier := frontier }

/-- OBLIGATION (not proved here), the statement that would let the row ReviewedTranscription-LaneDecode be accepted:
for every host context c and every `b : Slice U8`, the deployed slot `(AspisR1.NOC_HostCtx.sdk c).op50 b` is
`ok (Ok (carrier (decodeLane K b.val)))` when `decodeLane K b.val = some _` and `ok (Err InvalidAccountData)` when `none`,
with K instantiated by the frozen constants and decode_digest_canonical / V7_PAIR_EMPTY_ROOTS. The deployed slot is
`NCV_Reference.decode_lane_ref` (a hand-written reference crate) followed by NNH_LaneCarrier.native; the equality needs
loop-by-loop proofs for equal_loop, zero_loop, bytes32_loop, digest_loop and decode_frontier of that reference. -/
end PCVV_LaneDecodeRef
