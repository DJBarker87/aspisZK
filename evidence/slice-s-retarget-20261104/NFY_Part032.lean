import Lean
import NFY_Part031
import KMX_CopyMeaning
import NFY_Part005
import NEQ_UnwrapDomains
import NFY_Part030

-- BEGIN copied NED_EncoderCallDomains: evidence/slice-s-compose-20261029/NED_EncoderCallDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_EncoderCallDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
open NFY_NED_EncoderTrace

def LateShape (s : Statement) (xs : List Call) : Prop :=
  xs = [.late (common s).lane_transition NFY_NBN_LateResult.zero] ∨
  xs = [.late (common s).lane_transition NFY_NBN_LateResult.zero,.payment s]
def AnchorShape (s : Statement) (xs : List Call) : Prop :=
  xs = [.digest (common s).historical_global_anchor] ∨
  xs = [.digest (common s).historical_global_anchor,.late (common s).lane_transition NFY_NBN_LateResult.zero] ∨
  xs = [.digest (common s).historical_global_anchor,.late (common s).lane_transition NFY_NBN_LateResult.zero,.payment s]
def Shape (s : Statement) (xs : List Call) : Prop :=
  xs = [.validate s] ∨
  xs = [.validate s,.digest (common s).historical_global_anchor] ∨
  xs = [.validate s,.digest (common s).historical_global_anchor,.late (common s).lane_transition NFY_NBN_LateResult.zero] ∨
  xs = [.validate s,.digest (common s).historical_global_anchor,.late (common s).lane_transition NFY_NBN_LateResult.zero,.payment s]

theorem late_shape (s : Statement) (anchor : Array U8 32#usize) :
    LateShape s (lateStep s anchor).2 := by
  unfold lateStep
  dsimp only
  cases h : NFY_NBN_LateSummary.run enc (common s).lane_transition NFY_NBN_LateResult.zero with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok pair => cases pair with
    | mk status late => cases status with
      | Err e => simp only [h]; exact Or.inl rfl
      | Ok u => simp only [h]; exact Or.inr rfl

theorem anchor_shape (s : Statement) : AnchorShape s (anchorStep s).2 := by
  unfold anchorStep
  dsimp only
  cases h : enc (common s).historical_global_anchor with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok anchor =>
    simp only [h]
    rcases late_shape s anchor with one | two
    · rw [one]; exact Or.inr (Or.inl rfl)
    · rw [two]; exact Or.inr (Or.inr rfl)

theorem shape (s : Statement) : Shape s (run s).2 := by
  unfold run
  dsimp only
  cases h : NFY_NED_ExecutionComposition.validatorReference s with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok status => cases status with
    | Err e => simp only [h]; exact Or.inl rfl
    | Ok u =>
      simp only [h]
      rcases anchor_shape s with one | two | three
      · rw [one]; exact Or.inr (Or.inl rfl)
      · rw [two]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [three]; exact Or.inr (Or.inr (Or.inr rfl))

theorem validation_same (s arg : Statement)
    (reached : Call.validate arg ∈ (run s).2) : arg = s := by
  rcases shape s with one | two | three | four <;>
    simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.validate.injEq]

theorem payment_same (s arg : Statement)
    (reached : Call.payment arg ∈ (run s).2) : arg = s := by
  rcases shape s with one | two | three | four <;>
    simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.payment.injEq]

theorem digest_same (s : Statement) (arg : Array U32 8#usize)
    (reached : Call.digest arg ∈ (run s).2) : arg = (common s).historical_global_anchor := by
  rcases shape s with one | two | three | four <;>
    simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.digest.injEq]

theorem late_domain (s : Statement) (arg : NFY_NBN_LateSummary.Statement) (out : Slice U8)
    (reached : Call.late arg out ∈ (run s).2) :
    arg = (common s).lane_transition ∧ out = NFY_NBN_LateResult.zero ∧ out.length = 1520 := by
  have same : arg = (common s).lane_transition ∧ out = NFY_NBN_LateResult.zero := by
    rcases shape s with one | two | three | four <;>
      simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.late.injEq,and_self]
  obtain ⟨rfl,rfl⟩ := same
  refine ⟨rfl,rfl,?_⟩
  simp only [NFY_NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
  rfl

#print axioms late_shape
#print axioms anchor_shape
#print axioms shape
#print axioms validation_same
#print axioms payment_same
#print axioms digest_same
#print axioms late_domain
end NFY_NED_EncoderCallDomains
-- END copied NED_EncoderCallDomains
-- BEGIN copied NED_WindowExtensionality: evidence/slice-s-compose-20261029/NED_WindowExtensionality.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_WindowExtensionality
open Aeneas Aeneas.Std Result

theorem array_ext {α : Type} {n : Usize} (a b : Array α n)
    (point : ∀ i : Fin n.val,
      a.val[i.val]'(by have := a.property; omega) =
      b.val[i.val]'(by have := b.property; omega)) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem
  · have := a.property; have := b.property; omega
  · intro i hi hj
    exact point ⟨i,by have := a.property; omega⟩

theorem late_zero (out : Slice U8) (size : out.length = 1520)
    (point : ∀ i : Fin 1520, out.val[i.val]'(by change i.val < out.length; omega) = 0#u8) :
    out = NFY_NBN_LateResult.zero := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [NFY_NBN_LateResult.zero,Array.to_slice,Array.repeat_val,List.length_replicate]
    change out.length = 1520
    exact size
  · intro i hi hj
    have eq := point ⟨i,by change i < out.length at hi; omega⟩
    simpa only [NFY_NBN_LateResult.zero,Array.to_slice,Array.repeat_val,List.getElem_replicate] using eq

theorem prefix_frame {α : Type} (src dst : Nat → α) (start count offset : Nat)
    (end_before_late : start + count ≤ 144) :
    KMX_CopyMeaning.loop src dst start count (144+offset) = dst (144+offset) := by
  apply KMX_CopyMeaning.copy_frame
  right; omega

structure Write (α : Type) where
  source : Nat → α
  start : Nat
  count : Nat

def applyWrites {α : Type} : List (Write α) → (Nat → α) → Nat → α
  | [], dst => dst
  | w::ws, dst => applyWrites ws (KMX_CopyMeaning.loop w.source dst w.start w.count)

theorem prefixes_frame {α : Type} (writes : List (Write α)) (dst : Nat → α)
    (bounded : ∀ w ∈ writes, w.start+w.count ≤ 144) (offset : Nat) :
    applyWrites writes dst (144+offset) = dst (144+offset) := by
  induction writes generalizing dst with
  | nil => rfl
  | cons w ws ih =>
    rw [applyWrites,ih _ (by intro v hv; exact bounded v (by simp [hv]))]
    exact prefix_frame w.source dst w.start w.count offset (bounded w (by simp))

#print axioms array_ext
#print axioms late_zero
#print axioms prefix_frame
#print axioms prefixes_frame
end NFY_NED_WindowExtensionality
-- END copied NED_WindowExtensionality
-- BEGIN copied NEL_CopyArrayLaw: evidence/slice-s-compose4-20261101/NEL_CopyArrayLaw.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEL_CopyArrayLaw
open Aeneas Aeneas.Std Result

theorem list_inside {α : Type} (dst src : List α) (start k : Nat)
    (fits : start + src.length ≤ dst.length)
    (inside : start ≤ k ∧ k < start + src.length) :
    (dst.setSlice! start src)[k]? = src[k-start]? := by
  have hs : start ≤ dst.length := by omega
  have hroom : min src.length (dst.length-start) = src.length := Nat.min_eq_left (by omega)
  simp only [List.setSlice!, hroom, List.take_length]
  rw [List.append_assoc]
  have hlen : (dst.take start).length = start := by
    exact (List.length_take).trans (Nat.min_eq_left hs)
  rw [List.getElem?_append_right (by rw [hlen]; omega)]
  rw [List.getElem?_append_left (by rw [hlen]; omega)]
  rw [hlen]

theorem array_spec {N W : Usize} (dst : Array U8 N) (src : Array U8 W)
    (start k : Nat) (fits : start + W.val ≤ N.val) :
    (dst.setSlice! start src.val).val[k]? =
      if start ≤ k ∧ k < start + W.val then src.val[k-start]? else dst.val[k]? := by
  by_cases hi : start ≤ k ∧ k < start + W.val
  · rw [if_pos hi]
    change (dst.val.setSlice! start src.val)[k]? = _
    apply list_inside
    · simpa only [src.property,dst.property] using fits
    · simpa only [src.property] using hi
  · rw [if_neg hi]
    apply NFY_NEJ_ArrayFrame.array_frame
    · simpa only [src.property] using fits
    · simpa only [src.property] using (show k < start ∨ start + W.val ≤ k by omega)

/-- Exact KMX value-loop to emitted back-write association on one arbitrary
complete prestate. Both touched values and every external frame byte agree. -/
theorem loop_binding {N W : Usize} (dst : Array U8 N) (src : Array U8 W)
    (start k : Nat) (fits : start + W.val ≤ N.val) :
    KMX_CopyMeaning.loop (fun j => src.val[j-start]?) (fun j => dst.val[j]?) start W.val k =
      (dst.setSlice! start src.val).val[k]? := by
  rw [KMX_CopyMeaning.loop_spec, array_spec dst src start k fits]

#print axioms list_inside
#print axioms array_spec
#print axioms loop_binding
end NFY_NEL_CopyArrayLaw
-- END copied NEL_CopyArrayLaw
-- BEGIN copied NEL_SliceCopyLaw: evidence/slice-s-compose4-20261101/NEL_SliceCopyLaw.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEL_SliceCopyLaw
open Aeneas Aeneas.Std Result

/-- Dynamic borrowed slices use the same value law, preserving their complete
original allocation outside the copied window. No independent poststate occurs. -/
theorem loop_binding (dst src : Slice U8) (start k : Nat)
    (fits : start + src.length ≤ dst.length) :
    KMX_CopyMeaning.loop (fun j => src.val[j-start]?) (fun j => dst.val[j]?)
      start src.length k = (dst.setSlice! start src.val).val[k]? := by
  rw [KMX_CopyMeaning.loop_spec]
  change (if start ≤ k ∧ k < start + src.val.length then src.val[k-start]? else dst.val[k]?) =
    (dst.val.setSlice! start src.val)[k]?
  by_cases hi : start ≤ k ∧ k < start + src.val.length
  · rw [if_pos hi]
    exact (NFY_NEL_CopyArrayLaw.list_inside dst.val src.val start k fits hi).symm
  · rw [if_neg hi]
    exact (NFY_NEJ_ArrayFrame.list_frame dst.val src.val start k fits (by omega)).symm

#print axioms loop_binding
end NFY_NEL_SliceCopyLaw
-- END copied NEL_SliceCopyLaw
-- BEGIN copied NEL_LateDomains: evidence/slice-s-compose4-20261101/NEL_LateDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEL_LateDomains
open Aeneas Aeneas.Std Result

theorem child_window_lengths (out : Slice U8) (size : out.length = 1520) :
    ((out.val.drop 32).take 800).length = 800 ∧
    (out.val.drop 832).length = 688 := by
  change out.val.length = 1520 at size
  simp only [List.length_take,List.length_drop,size]
  decide

/-- Snapshot and afterstate windows partition the suffix; header bytes belong
neither to child, including when a child rejects. -/
theorem child_windows (k : Nat) :
    ((32 ≤ k ∧ k < 832) ∨ (832 ≤ k ∧ k < 1520)) ↔ 32 ≤ k ∧ k < 1520 := by omega

theorem header_frame (out src : Slice U8) (size : out.length = 1520)
    (source_size : src.length = 800) (k : Nat) (header : k < 32) :
    (out.setSlice! 32 src.val).val[k]? = out.val[k]? := by
  apply NFY_NEJ_ArrayFrame.list_frame
  · change 32 + src.length ≤ out.length
    omega
  · exact Or.inl header

#print axioms child_window_lengths
#print axioms child_windows
#print axioms header_frame
end NFY_NEL_LateDomains
-- END copied NEL_LateDomains
-- BEGIN copied NEM_SnapshotBorrow: evidence/slice-s-compose5-20261102/NEM_SnapshotBorrow.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEM_SnapshotBorrow
open Aeneas Aeneas.Std Result

/-- The actual emitted borrow and its back function, on the same allocation.
The poststate is arbitrary: this is not a one-cell mutation restriction. -/
theorem rejoin (out : Slice U8) (size : out.length = 1520) :
    ∃ child back,
      core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
        out {start := 32#usize, «end» := 832#usize} = ok (child,back) ∧
      child.length = 800 ∧ ∀ post : Slice U8, back post = out.setSlice! 32 post.val := by
  have guard : (32#usize) ≤ 832#usize ∧ (832#usize).val ≤ out.length := by
    constructor
    · decide
    · rw [size]; decide
  simp only [core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,if_pos guard]
  refine ⟨_,_,rfl,?_,?_⟩
  · have len : out.val.length = 1520 := size
    simp only [Slice.length,List.slice,List.length_take,List.length_drop,len]
    decide
  · intro post
    rfl

/-- All possible 800-byte child poststates and every external allocation byte. -/
theorem poststate (out post : Slice U8) (size : out.length = 1520)
    (post_size : post.length = 800) (k : Nat) :
    (out.setSlice! 32 post.val).val[k]? =
      if 32 ≤ k ∧ k < 832 then post.val[k-32]? else out.val[k]? := by
  rw [← NFY_NEL_SliceCopyLaw.loop_binding out post 32 k (by rw [post_size,size]; decide)]
  rw [KMX_CopyMeaning.loop_spec,post_size]

/-- The later afterstate write preserves the exact child's whole poststate. -/
theorem after_preserves_child (out post : Slice U8) (size : out.length = 1520)
    (after : Array U8 688#usize) (k : Nat) (earlier : k < 832) :
    ((out.setSlice! 32 post.val).setSlice! 832 after.val).val[k]? =
      (out.setSlice! 32 post.val).val[k]? := by
  apply NFY_NEJ_ArrayFrame.list_frame
  · have len : out.val.length = 1520 := size
    simp only [Slice.setSlice!,List.length_setSlice!,after.property,len]
    decide
  · exact Or.inl earlier

#print axioms rejoin
#print axioms poststate
#print axioms after_preserves_child
end NFY_NEM_SnapshotBorrow
-- END copied NEM_SnapshotBorrow
-- BEGIN copied NEM_LateOracle: evidence/slice-s-compose5-20261102/NEM_LateOracle.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEM_LateOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NFY_NBN_LateSummary (Statement)
abbrev Live := NFY_NBH_LiveValidator.Snapshot → Slice U8 →
  Result (core.result.Result Unit NFY_NBH_LiveValidator.Error × Slice U8)
abbrev After := NFY_NBH_Validators.Afterstate →
  Result (core.result.Result (Array U8 688#usize) NFY_NBH_Validators.AfterError)

def tail (live : Live) (after : After) (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit NFY_NBN_LateSummary.Error × Slice U8) := do
  let i7 ← 32#usize + pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  let (child,back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start := 32#usize, «end» := i7}
  let (r,post) ← live s.live_snapshot child
  match r with
  | .Err e => ok (.Err (.Snapshot e),back post)
  | .Ok _ =>
    let r2 ← after s.candidate_afterstate
    match r2 with
    | .Err e => ok (.Err (.Afterstate e),back post)
    | .Ok bytes =>
      let (dest,back2) ← core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) (back post) {start := i7}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dest bytes.to_slice
      ok (.Ok (),back2 copied)

def run (live : Live) (after : After) (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit NFY_NBN_LateSummary.Error × Slice U8) :=
  if output.length ≠ 1520 then ok (.Err .WrongLength,output)
  else if U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
      some s.candidate_afterstate.next_pair_index then ok (.Err .AfterstateIndexMismatch,output)
  else do
    let filled ← core.slice.Slice.fill core.clone.CloneU8 output 0#u8
    NFY_NBN_LatePrepare.run filled (tail live after s)

theorem tail_substitution (s : Statement) (out : Slice U8) :
    tail pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
      pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 s out =
      NFY_NBN_LateSummary.tail NFY_NED_ValidatorTrace.enc s out := by
  unfold tail NFY_NBN_LateSummary.tail
  simp only [NFY_NED_ValidatorTrace.enc,← NFY_NED_SubtreeComposition.live_encode,← NFY_NED_SubtreeComposition.after_encode]
  rfl

theorem run_substitution (s : Statement) (out : Slice U8) :
    run pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
      pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 s out =
      NFY_NBN_LateSummary.run NFY_NED_ValidatorTrace.enc s out := by
  have same : tail pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
      pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 s =
      NFY_NBN_LateSummary.tail NFY_NED_ValidatorTrace.enc s := funext (tail_substitution s)
  unfold run NFY_NBN_LateSummary.run
  rw [same]

def late : NFY_NEE_ValidatorMutation.Late :=
  pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1

theorem value_and_frame (s : Statement) (out : Slice U8) :
    run pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
      pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 s out = late s out :=
  (run_substitution s out).trans (NFY_NED_SubtreeComposition.late_encode s out)

theorem late_reached (s : NFY_NBN_StatementResult.Statement) (a : Statement) (out : Slice U8)
    (_reached : NFY_NED_ValidatorTrace.Call.late a out ∈
      (NFY_NEE_ValidatorOracle.run NFY_NEM_PaymentReached.pay NFY_NEM_LaneReached.lane late s).2) :
    NFY_NEE_ValidatorMutation.ignore (late a out) =
      NFY_NEE_ValidatorMutation.ignore (NFY_NBN_LateSummary.run NFY_NED_ValidatorTrace.enc a out) :=
  congrArg NFY_NEE_ValidatorMutation.ignore (NFY_NED_SubtreeComposition.late_encode a out).symm

#print axioms tail_substitution
#print axioms run_substitution
#print axioms value_and_frame
#print axioms late_reached
end NFY_NEM_LateOracle
-- END copied NEM_LateOracle
-- BEGIN copied NEM_ValidatorComposed: evidence/slice-s-compose5-20261102/NEM_ValidatorComposed.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEM_ValidatorComposed
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult

/-- Concrete model G for the three SAME calls certified natively. The hybrid
native correspondence is checked separately by NEM_validate; this theorem
introduces no inner callee domain, interpretation, or bridge hypothesis. -/
theorem result_state_effects {State : Type} (s : Statement) (state : State) :
    let observed := NFY_NEE_ValidatorOracle.run NFY_NEM_PaymentReached.pay NFY_NEM_LaneReached.lane
      NFY_NEM_LateOracle.late s
    (observed.1,state,observed.2) =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       state,(NFY_NED_ValidatorTrace.run s).2) := by
  have same := NFY_NEE_ReachedRootModel.result_and_effects NFY_NEM_PaymentReached.pay
    NFY_NEM_LaneReached.lane NFY_NEM_LateOracle.late s
    (fun a reached => NFY_NEM_PaymentReached.payment_reached NFY_NEM_LaneReached.lane
      NFY_NEM_LateOracle.late s a reached)
    (fun d reached => NFY_NEM_LaneReached.lane_reached NFY_NEM_LateOracle.late s d reached)
    (fun a out reached => NFY_NEM_LateOracle.late_reached s a out reached)
  rw [same]

#print axioms result_state_effects
end NFY_NEM_ValidatorComposed
-- END copied NEM_ValidatorComposed
-- BEGIN copied NEQ_CommonDecode: evidence/slice-s-compose6-20261102/NEQ_CommonDecode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEQ_CommonDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Common := pool_v1.payment_relation.CommonPublicV1
abbrev Err := pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev DigestCall := Array U8 32#usize → Result (core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError)
abbrev Validate := Common → Result (core.result.Result Unit Err)
attribute [local instance] Classical.propDecidable

def run (decode : DigestCall) (validate : Validate) (b : Array U8 216#usize) :
    Result (core.result.Result Common Err) := do
  if NFY_NBP_CommonDecode.asset b >= 2147483647#u32 then ok (.Err .NonCanonicalAssetId)
  else
    let anchor ← decode (NBP_Read.chunk b 80 (by decide))
    match anchor with
    | .Err _ => ok (.Err .NonCanonicalDigest)
    | .Ok a =>
      let nullifier ← decode (NBP_Read.chunk b 112 (by decide))
      match nullifier with
      | .Err _ => ok (.Err .NonCanonicalDigest)
      | .Ok n =>
        let c := NFY_NBP_CommonDecode.common b a n
        let valid ← validate c
        match valid with
        | .Err e => ok (.Err e)
        | .Ok _ => ok (.Ok c)

theorem substitution (b : Array U8 216#usize) :
    run atomic_statement.decode_digest_canonical pool_v1.payment_relation.validate_common b =
      ok (NFY_NBP_CommonDecode.decoded b) := by
  unfold run NFY_NBP_CommonDecode.decoded
  simp only [NFY_NBP_DigestDecode.result,NFY_NBG_PaymentChecks.common_result,bind_tc_ok]
  by_cases invalid : NFY_NBP_CommonDecode.asset b >= 2147483647#u32
  · simp only [if_pos invalid]
  · simp only [if_neg invalid]
    cases a : NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 80 (by decide)) with
    | Err e => rfl
    | Ok anchor =>
      dsimp only
      cases n : NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 112 (by decide)) with
      | Err e => rfl
      | Ok nullifier =>
        dsimp only
        cases NFY_NBG_PaymentChecks.common (NFY_NBP_CommonDecode.common b anchor nullifier) <;> rfl

theorem result_state_effects {State : Type} (b : Array U8 216#usize) (state : State) :
    (run atomic_statement.decode_digest_canonical pool_v1.payment_relation.validate_common b,state,([] : List Unit)) =
      (pool_v1.payment_relation.decode_common b,state,[]) := by
  rw [substitution,NFY_NBP_CommonDecode.result]

#print axioms substitution
#print axioms result_state_effects
end NFY_NEQ_CommonDecode
-- END copied NEQ_CommonDecode
-- BEGIN copied NBP_TransferDecode: lean/NBP_TransferDecode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_TransferDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_PaymentModel

theorem fixed (b : Array U8 216#usize) :
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 b.to_slice = ok (transfer_decoded b) := by
  have eq32 : ∀ h, Usize.ofNatCore 32 h = 32#usize := fun _ => rfl
  have eq216 : ∀ h, Usize.ofNatCore 216 h = 216#usize := fun _ => rfl
  have tail32 : (b.val.drop 184).take 32 = b.val.drop 184 := by
    apply List.take_of_length_le
    simp [b.property]
  have fee : (core.num.U32.to_le_bytes 0#u32).val = [0#u8,0#u8,0#u8,0#u8] := by simp [core.num.U32.to_le_bytes,BitVec.toLEBytes]; apply U8.bv_eq_imp_eq; rfl
  simp [fee,eq32,eq216,tail32,Slice.drop,pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1,
    NFY_NBG_Header.header_result,NFY_NBP_CommonDecode.result,NFY_NBG_PaymentValidators.transfer_result,
    pool_v1.payment_relation.ASSET_ID_OFFSET,pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,
    core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Array.to_slice,Slice.length,Slice.len,b.property,
    core.array.TryFromArrayCopySlice.try_from,core.array.TryFromSharedArraySlice.try_from,
    atomic_statement.unwrap_fixed_slice,aspis_core.field.P,
    NFY_NBP_DigestDecode.result,NFY_NBG_PaymentChecks.common_result,
    transfer_decoded,transfer_public,NBP_Read.chunk,lift,bind_tc_ok,List.slice,
    pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
    pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    pool_v1.payment_relation.POOL_V1_CANONICAL_FEE,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice,NFY_NBG_Header.slice_equal,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once,
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once,
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  repeat' split
  all_goals simp_all

/-- All slice lengths, including rejection before any fixed-width read. -/
theorem result (bytes : Slice U8) :
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 bytes =
      if h : bytes.val.length=216 then ok (transfer_decoded (⟨bytes.val,h⟩ : Array U8 216#usize))
      else ok (.Err .WrongLength) := by
  by_cases h : bytes.val.length=216
  · rw [dif_pos h]
    change pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 (Array.to_slice (⟨bytes.val,h⟩ : Array U8 216#usize)) = _
    exact fixed _
  · rw [dif_neg h]
    simp [pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1,core.array.TryFromSharedArraySlice.try_from,
      Slice.len,Slice.length,h,AspisR1TerminalDecoder.core.result.Result.map_err,
      pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,
      pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
#print axioms result
#print axioms fixed
end NFY_NBP_TransferDecode
-- END copied NBP_TransferDecode
-- BEGIN copied NBP_WithdrawalDecode: lean/NBP_WithdrawalDecode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBP_WithdrawalDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBP_PaymentModel

theorem fixed (b : Array U8 216#usize) :
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 b.to_slice = ok (withdrawal_decoded b) := by
  have eq32 : ∀ h, Usize.ofNatCore 32 h = 32#usize := fun _ => rfl
  have eq216 : ∀ h, Usize.ofNatCore 216 h = 216#usize := fun _ => rfl
  have tail32 : (b.val.drop 184).take 32 = b.val.drop 184 := by
    apply List.take_of_length_le
    simp [b.property]
  simp [eq32,eq216,tail32,Slice.drop,pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1,
    NFY_NBG_Header.header_result,NFY_NBP_CommonDecode.result,NFY_NBG_PaymentValidators.withdrawal_result,
    pool_v1.payment_relation.ASSET_ID_OFFSET,pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,
    core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Array.to_slice,Slice.length,Slice.len,b.property,
    core.array.TryFromArrayCopySlice.try_from,core.array.TryFromSharedArraySlice.try_from,
    atomic_statement.unwrap_fixed_slice,aspis_core.field.P,
    NFY_NBP_DigestDecode.result,NFY_NBG_PaymentChecks.common_result,
    withdrawal_decoded,withdrawal_public,NBP_Read.chunk,lift,bind_tc_ok,List.slice,
    pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
    pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    pool_v1.payment_relation.POOL_V1_CANONICAL_FEE,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice,NFY_NBG_Header.slice_equal,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once,
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError,
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  repeat' split
  all_goals simp_all

/-- All slice lengths, including rejection before any fixed-width read. -/
theorem result (bytes : Slice U8) :
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes =
      if h : bytes.val.length=216 then ok (withdrawal_decoded (⟨bytes.val,h⟩ : Array U8 216#usize))
      else ok (.Err .WrongLength) := by
  by_cases h : bytes.val.length=216
  · rw [dif_pos h]
    change pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 (Array.to_slice (⟨bytes.val,h⟩ : Array U8 216#usize)) = _
    exact fixed _
  · rw [dif_neg h]
    simp [pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1,core.array.TryFromSharedArraySlice.try_from,
      Slice.len,Slice.length,h,AspisR1TerminalDecoder.core.result.Result.map_err,
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
#print axioms result
#print axioms fixed
end NFY_NBP_WithdrawalDecode
-- END copied NBP_WithdrawalDecode
-- BEGIN copied NEQ_PaymentDecode: evidence/slice-s-compose6-20261102/NEQ_PaymentDecode.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEQ_PaymentDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NFY_NBP_PaymentModel
attribute [local instance] Classical.propDecidable
abbrev CommonCall := Array U8 216#usize → Result (core.result.Result C E)
abbrev Decode := NFY_NEQ_CommonDecode.DigestCall
abbrev TransferCheck := T → Result (core.result.Result Unit E)
abbrev WithdrawalCheck := W → Result (core.result.Result Unit E)

def transferRun (common : CommonCall) (decode : Decode) (validate : TransferCheck)
    (b : Array U8 216#usize) : Result (core.result.Result T E) := do
  let h ← pool_v1.payment_relation.require_header b
    pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer
  match h with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    if (b.val.drop 148).take 4 ≠ List.replicate 4 0#u8 then ok (.Err .NonZeroReserved)
    else
      let c ← common b
      match c with
      | .Err e => ok (.Err e)
      | .Ok c =>
        let r ← decode (NBP_Read.chunk b 152 (by decide))
        match r with
        | .Err _ => ok (.Err .NonCanonicalDigest)
        | .Ok r =>
          let z ← decode (NBP_Read.chunk b 184 (by decide))
          match z with
          | .Err _ => ok (.Err .NonCanonicalDigest)
          | .Ok z =>
            let p := transfer_public c r z
            let valid ← validate p
            match valid with | .Err e => ok (.Err e) | .Ok _ => ok (.Ok p)

def withdrawalRun (common : CommonCall) (decode : Decode) (validate : WithdrawalCheck)
    (b : Array U8 216#usize) : Result (core.result.Result W E) := do
  let h ← pool_v1.payment_relation.require_header b
    pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal
  match h with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let c ← common b
    match c with
    | .Err e => ok (.Err e)
    | .Ok c =>
      let z ← decode (NBP_Read.chunk b 184 (by decide))
      match z with
      | .Err _ => ok (.Err .NonCanonicalDigest)
      | .Ok z =>
        let p := withdrawal_public c b z
        let valid ← validate p
        match valid with | .Err e => ok (.Err e) | .Ok _ => ok (.Ok p)

theorem transfer_substitution (b : Array U8 216#usize) :
    transferRun pool_v1.payment_relation.decode_common atomic_statement.decode_digest_canonical
      pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 b =
      ok (transfer_decoded b) := by
  unfold transferRun transfer_decoded
  simp only [NFY_NBG_Header.header_result,NFY_NBP_CommonDecode.result,NFY_NBP_DigestDecode.result,
    NFY_NBG_PaymentValidators.transfer_result,bind_tc_ok]
  cases h : NFY_NBG_Header.expected b pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer with
  | Err e => rfl
  | Ok u =>
    dsimp only
    by_cases fee : (b.val.drop 148).take 4 ≠ List.replicate 4 0#u8
    · simp only [if_pos fee]
    · simp only [if_neg fee]
      cases c : NFY_NBP_CommonDecode.decoded b with
      | Err e => rfl
      | Ok common =>
        dsimp only
        cases r : NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 152 (by decide)) with
        | Err e => rfl
        | Ok recipient =>
          dsimp only
          cases z : NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 184 (by decide)) with
          | Err e => rfl
          | Ok change =>
            dsimp only
            cases NFY_NBG_PaymentValidators.transfer (transfer_public common recipient change) <;> rfl

theorem withdrawal_substitution (b : Array U8 216#usize) :
    withdrawalRun pool_v1.payment_relation.decode_common atomic_statement.decode_digest_canonical
      pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 b =
      ok (withdrawal_decoded b) := by
  unfold withdrawalRun withdrawal_decoded
  simp only [NFY_NBG_Header.header_result,NFY_NBP_CommonDecode.result,NFY_NBP_DigestDecode.result,
    NFY_NBG_PaymentValidators.withdrawal_result,bind_tc_ok]
  cases h : NFY_NBG_Header.expected b pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal with
  | Err e => rfl
  | Ok u =>
    dsimp only
    cases c : NFY_NBP_CommonDecode.decoded b with
    | Err e => rfl
    | Ok common =>
      dsimp only
      cases z : NFY_NBP_DigestDecode.decoded (NBP_Read.chunk b 184 (by decide)) with
      | Err e => rfl
      | Ok change =>
        dsimp only
        cases NFY_NBG_PaymentValidators.withdrawal (withdrawal_public common b change) <;> rfl

def transferFull (bytes : Slice U8) : Result (core.result.Result T E) :=
  if h : bytes.val.length=216 then
    transferRun pool_v1.payment_relation.decode_common atomic_statement.decode_digest_canonical
      pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 ⟨bytes.val,h⟩
  else ok (.Err .WrongLength)

def withdrawalFull (bytes : Slice U8) : Result (core.result.Result W E) :=
  if h : bytes.val.length=216 then
    withdrawalRun pool_v1.payment_relation.decode_common atomic_statement.decode_digest_canonical
      pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 ⟨bytes.val,h⟩
  else ok (.Err .WrongLength)

theorem transfer_result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (transferFull bytes,state,([] : List Unit)) =
      (pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 bytes,state,[]) := by
  unfold transferFull
  rw [NFY_NBP_TransferDecode.result]
  by_cases h : bytes.val.length=216
  · rw [dif_pos h,dif_pos h,transfer_substitution]
  · rw [dif_neg h,dif_neg h]

theorem withdrawal_result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (withdrawalFull bytes,state,([] : List Unit)) =
      (pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes,state,[]) := by
  unfold withdrawalFull
  rw [NFY_NBP_WithdrawalDecode.result]
  by_cases h : bytes.val.length=216
  · rw [dif_pos h,dif_pos h,withdrawal_substitution]
  · rw [dif_neg h,dif_neg h]

#print axioms transfer_substitution
#print axioms withdrawal_substitution
#print axioms transfer_result_state_effects
#print axioms withdrawal_result_state_effects
end NFY_NEQ_PaymentDecode
-- END copied NEQ_PaymentDecode

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
