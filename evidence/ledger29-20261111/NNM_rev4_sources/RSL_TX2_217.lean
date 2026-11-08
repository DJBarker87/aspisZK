/-
TX2:217  programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release
Frozen signature (r1_pool_adapter.rs:448):
  fn decode_lane_from_pool_release(bytes: &[u8])
      -> Result<Box<PoolV1PairForestLaneStateV1>, ProgramError>
Route: emitted body under (bm) (owned layer, no guard).
Children: decode_digest_canonical (CLOSED TX2:146, NFY_Part005) at each of the
21 digest windows; V7_PAIR_EMPTY_ROOTS (frozen constant table).
Own-input domain ((bf)(2)): none.  The function is total over every byte slice.
Effects: none except the final Box allocation (abort arm, (bl)(3)).
-/
import RSL_Pool
set_option autoImplicit false

namespace RSL.TX2_217

/-- `decode_digest_canonical(&[u8;32])` (CLOSED TX2:146): eight little-endian
u32 limbs, each `< P = 0x7fffffff`, else Err (mapped by the caller). -/
def decodeDigestCanonical (b : Bytes) : Option Digest :=
  let ws := (List.range 8).map (fun i =>
    le32 (b.getD (4*i) 0) (b.getD (4*i+1) 0) (b.getD (4*i+2) 0) (b.getD (4*i+3) 0))
  if ws.all (fun w => decide (w < P31)) then some ws else none

/-- Header test of lines 452-463 (the `||` chain; every failure is
InvalidAccountData, and short-circuiting only avoids out-of-range reads). -/
def headerBad (b : Bytes) : Bool :=
  b.length != LANE_ACCOUNT_BYTES
  || slice b 0 4 != LANE_MAGIC
  || b.getD 4 0 != LANE_VERSION
  || decide (LANE_COUNT ≤ (b.getD 5 0).toNat)
  || b.getD 6 0 != (8 : UInt8)
  || b.getD 7 0 != (20 : UInt8)
  || slice b 8 40 != FORMAT_BINDING
  || (slice b 73 LANE_HEADER_BYTES).any (· != 0)

def treeHeaderBad (t : Bytes) : Bool :=
  slice t 0 4 != TREE_STATE_MAGIC
  || t.getD 4 0 != TREE_STATE_VERSION
  || t.getD 5 0 != (20 : UInt8)
  || t.getD 6 0 != TREE_HASH_VERSION
  || t.getD 7 0 != DIGEST_ENCODING_VERSION

/-- The frontier loop (lines 492-503), level 0..19 in order: decode the node
(Err -> InvalidAccountData) and, when bit `level` of next_leaf_index is 0,
require the pinned empty root. -/
def frontierLoop (t : Bytes) (next : UInt64) : Nat → Option (List Digest)
  | 0 => some []
  | n + 1 =>
    match frontierLoop t next n with
    | none => none
    | some acc =>
      let level := n
      let start := 48 + 32 * level
      match decodeDigestCanonical (slice t start (start + 32)) with
      | none => none
      | some node =>
        if (next >>> level.toUInt64) &&& 1 == 0 && node != EMPTY_ROOTS.getD level [] then none
        else some (acc ++ [node])

/-- The complete pure part of the body: `some lane` exactly when every check of
lines 452-507 passes, with the exact field values of lines 508-516. -/
def laneDecode (b : Bytes) : Option LaneState :=
  if headerBad b then none else
  let masterBytes := slice b 40 72
  if masterBytes.all (· == 0) then none else
  let t := b.drop LANE_HEADER_BYTES
  if treeHeaderBad t then none else
  let next := le64 (slice t 8 16)
  if decide (PAIR_CAPACITY < next) then none else
  match decodeDigestCanonical (slice t 16 48) with
  | none => none
  | some root =>
    match frontierLoop t next TREE_DEPTH with
    | none => none
    | some frontier =>
      if next == 0 && root != EMPTY_ROOTS.getD TREE_DEPTH [] then none
      else if h : masterBytes.length = 32 then
        some { bump := b.getD 72 0, master := ⟨masterBytes, h⟩, lane_id := b.getD 5 0,
               tree := { next_leaf_index := next, root := root, frontier := frontier } }
      else none

/-- Reference: every Err is InvalidAccountData with no effect; on success one
Box allocation (abort arm) then Ok with the exact decoded lane. -/
def Ref (bytes : Bytes) : RS LaneState :=
  match laneDecode bytes with
  | none => RS.throw .invalidAccountData
  | some lane => RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure lane)

/-- Own-input domain: none. -/
def Domain (_bytes : Bytes) : Prop := True

/-- RowSpec_217: the complete obligation of the actual function at SAME argument. -/
def RowSpec_217 (decode_lane_from_pool_release : Bytes → Env → Obs (Except ProgramError LaneState)) :
    Prop :=
  ∀ bytes env, Domain bytes → Ref bytes env (decode_lane_from_pool_release bytes env)

/-! ## Rejection of trivial implementations -/

/-- A well-formed lane image: next_leaf_index = 2^20-1 (no empty-root
constraint), zero root and frontier, master = [1;32]. -/
@[irreducible] def witness : Bytes :=
  LANE_MAGIC ++ [2, 0, 8, 20] ++ FORMAT_BINDING ++ List.replicate 32 1 ++ [0]
  ++ List.replicate 7 0
  ++ TREE_STATE_MAGIC ++ [1, 20, 3, 1] ++ [0xff, 0xff, 0x0f, 0, 0, 0, 0, 0]
  ++ List.replicate 32 0 ++ List.replicate (32 * 20) 0

theorem witness_decodes : (laneDecode witness).isSome = true := by decide +kernel

/-- No constant-Err implementation satisfies RowSpec_217. -/
theorem rejects_constErr (e : ProgramError) :
    ¬ RowSpec_217 (constErr e) := by
  intro h
  have hw : Ref witness env0 (constErr e witness env0) := h _ _ True.intro
  have hs := witness_decodes
  unfold Ref at hw
  revert hw hs
  generalize laneDecode witness = d
  intro hw hs
  cases d with
  | none => simp at hs
  | some lane =>
    rcases RS.alloc_pure_obs lane env0 _ hw with h1 | h1 <;> simp [constErr] at h1

/-- No constant-abort implementation satisfies RowSpec_217 (the empty slice
must return Err(InvalidAccountData) with no abort). -/
theorem rejects_constAbort :
    ¬ RowSpec_217 constAbort := by
  intro h
  have hw := h [] env0 trivial
  have hn : laneDecode [] = none := by decide +kernel
  unfold Ref at hw
  revert hw hn
  generalize laneDecode [] = d
  intro hw hn
  subst hn
  simp [RS.throw, Spec.pure, constAbort] at hw

end RSL.TX2_217
