import Lean
import NFY_Part024
import NFY_Part006
import RPz7_S2K_DigestBytes
import NBH_ArrayEq

-- BEGIN copied NBN_LateResult: lean/NBN_LateResult.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NBN_LateResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
abbrev Statement := PoolV1PairLatePublicStatementV1

theorem factor (s : Statement) (output : Slice U8)
    (size : output.length = 1520)
    (index : U64.checked_add s.live_snapshot.next_pair_index 1#u64 =
      some s.candidate_afterstate.next_pair_index) :
    encode_pool_v1_pair_late_public_statement_v1 s output =
      (do let filled ← core.slice.Slice.fill core.clone.CloneU8 output 0#u8
          NFY_NBN_LatePrepare.run filled (NFY_NBN_LateTail.run s)) := by
  have len : Slice.len output = 1520#usize := by scalar_tac
  simp only [encode_pool_v1_pair_late_public_statement_v1,
    AspisR1.NFY_JFs_LateConstants.size,bind_tc_ok,len,bne_self_eq_false,if_false,
    lift,NFY_NBK_LatePreflight.option_ne,index,ne_eq,not_true_eq_false,decide_false]
  have tail_eq : NFY_NBN_LateFactor.raw s = NFY_NBN_LateTail.run s :=
    funext (NFY_NBN_LateFactor.raw_eq s)
  rw [← tail_eq]
  rfl

def zero : Slice U8 := (Array.repeat 1520#usize 0#u8).to_slice
def header : Slice U8 := NFY_NBN_LatePrepare.value zero

theorem header_length : header.length = 1520 := by
  simp only [header,NFY_NBN_LatePrepare.value,Slice.length,zero,Array.to_slice,
    Array.repeat_val,List.length_setSlice!,List.length_set,List.length_replicate]
  rfl

theorem source (s : Statement) (output : Slice U8) :
    encode_pool_v1_pair_late_public_statement_v1 s output =
      if output.length ≠ 1520 then ok (.Err .WrongLength,output)
      else if U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
          some s.candidate_afterstate.next_pair_index then
        ok (.Err .AfterstateIndexMismatch,output)
      else ok (NFY_NBN_LateTail.status s,NFY_NBN_LateTail.value s header) := by
  by_cases size : output.length = 1520
  · rw [if_neg (not_not.mpr size)]
    by_cases index : U64.checked_add s.live_snapshot.next_pair_index 1#u64 =
      some s.candidate_afterstate.next_pair_index
    · rw [if_neg (not_not.mpr index),factor s output size index,NFY_NBK_Fill.source]
      have filled : NFY_NBK_Fill.value output 0#u8 = zero := by
        apply Subtype.ext
        change List.replicate output.length 0#u8 = List.replicate 1520 0#u8
        rw [size]
      rw [filled]
      simp only [bind_tc_ok]
      rw [NFY_NBN_LatePrepare.exact zero (by simp only [zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]; rfl)]
      exact NFY_NBN_LateTail.exact s header header_length
    · rw [if_pos index]
      exact NFY_NBK_LatePreflight.wrong_index s output size index
  · rw [if_pos size]
    exact NFY_NBK_LatePreflight.wrong_length s output size

#print axioms factor
#print axioms header_length
#print axioms source
end NFY_NBN_LateResult
-- END copied NBN_LateResult
-- BEGIN copied NBN_LateSummary: lean/NBN_LateSummary.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_LateSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
abbrev Statement := PoolV1PairLatePublicStatementV1
abbrev Error := PoolV1PairLatePublicStatementErrorV1
abbrev Encode := NFY_NBN_EncoderSummary.Encode
abbrev NBN_Dep_DigestEncodeCanonical := NFY_NBN_EncoderSummary.NBN_Dep_DigestEncodeCanonical

def tail (encode : NFY_NBN_EncoderSummary.Encode) (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit Error × Slice U8) := do
  let i7 ← 32#usize + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  let (s15, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start := 32#usize, «end» := i7}
  let (r, s16) ← NFY_NBN_EncoderSummary.live encode s.live_snapshot s15
  match r with
  | .Err e => ok (.Err (.Snapshot e), back s16)
  | .Ok _ =>
    let r2 ← NFY_NBN_EncoderSummary.after encode s.candidate_afterstate
    match r2 with
    | .Err e => ok (.Err (.Afterstate e), back s16)
    | .Ok bytes =>
      let (dest, back2) ← core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) (back s16) {start := i7}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dest bytes.to_slice
      ok (.Ok (), back2 copied)


theorem tail_source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : Statement) (output : Slice U8) : tail encode s output = NFY_NBN_LateTail.run s output := by
  unfold tail NFY_NBN_LateTail.run
  simp only [NFY_NBN_EncoderSummary.live_source encode lower,NFY_NBN_EncoderSummary.after_source encode lower]
  rfl

def run (encode : Encode) (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit Error × Slice U8) :=
  if output.length ≠ 1520 then ok (.Err .WrongLength,output)
  else if U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
      some s.candidate_afterstate.next_pair_index then ok (.Err .AfterstateIndexMismatch,output)
  else do
    let filled ← core.slice.Slice.fill core.clone.CloneU8 output 0#u8
    NFY_NBN_LatePrepare.run filled (tail encode s)

theorem source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : Statement) (output : Slice U8) :
    run encode s output = encode_pool_v1_pair_late_public_statement_v1 s output := by
  unfold run
  by_cases size : output.length = 1520
  · rw [if_neg (not_not.mpr size)]
    by_cases index : U64.checked_add s.live_snapshot.next_pair_index 1#u64 =
        some s.candidate_afterstate.next_pair_index
    · rw [if_neg (not_not.mpr index)]
      have same : tail encode s = NFY_NBN_LateTail.run s := funext (tail_source encode lower s)
      rw [same]
      exact (NFY_NBN_LateResult.factor s output size index).symm
    · rw [if_pos index]
      exact (NFY_NBK_LatePreflight.wrong_index s output size index).symm
  · rw [if_pos size]
    exact (NFY_NBK_LatePreflight.wrong_length s output size).symm

#print axioms tail_source
#print axioms source
end NFY_NBN_LateSummary
-- END copied NBN_LateSummary
-- BEGIN copied NBN_OutputLane: lean/NBN_OutputLane.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_OutputLane
attribute [local instance] Classical.propDecidable
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_forest_accounts
abbrev Digest := Array U32 8#usize

def first (d : Digest) : U8 := (DigestBytes.bytes d).val[0]!

theorem first_source (d : Digest) : first_canonical_byte d = ok (first d) := by
  unfold first_canonical_byte
  rw [DigestBytes.exact]
  simp [Array.index_usize,first,(DigestBytes.bytes d).property]

def result (d : Digest) : core.result.Result U8 PoolV1PairForestAccountErrorV1 :=
  if NBD_DigestInduction.Canonical d then .Ok (first d &&& 7#u8)
  else .Err .NonCanonicalDigest

theorem source (d : Digest) : pool_v1_pair_forest_output_lane_v1 d = ok (result d) := by
  unfold pool_v1_pair_forest_output_lane_v1
  rw [NBD_DigestInduction.same_scanner,NBD_DigestInduction.source]
  simp only [bind_tc_ok]
  by_cases h : NBD_DigestInduction.Canonical d
  · simp only [h,decide_true,if_true,first_source,bind_tc_ok,lift,result]
  · simp [h,result]

#print axioms first_source
#print axioms source
end NFY_NBN_OutputLane
-- END copied NBN_OutputLane
-- BEGIN copied NBN_FirstByteDependency: lean/NBN_FirstByteDependency.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_FirstByteDependency
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open NFY_NBN_DigestResultDependency
attribute [local instance] Classical.propDecidable

def first (encode : Encode) (d : Digest) : Result U8 := do
  let bytes ← encode d
  Array.index_usize bytes 0#usize

def lane (encode : Encode) (d : Digest) :
    Result (core.result.Result U8 pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) :=
  if NBD_DigestInduction.Canonical d then do
    let b ← first encode d
    ok (.Ok (b &&& 7#u8))
  else ok (.Err .NonCanonicalDigest)

theorem first_source (encode : Encode) (lower : NBN_Dep_DigestEncodeRaw encode) (d : Digest) :
    first encode d = pool_v1.pair_forest_accounts.first_canonical_byte d := by
  unfold first pool_v1.pair_forest_accounts.first_canonical_byte
  rw [lower d,DigestBytes.exact]

theorem lane_source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode) (d : Digest) :
    lane encode d = pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 d := by
  rw [NFY_NBN_OutputLane.source]
  by_cases good : NBD_DigestInduction.Canonical d
  · simp only [lane,good,if_true,first,lower d good,bind_tc_ok]
    simp [Array.index_usize,(DigestBytes.bytes d).property,NFY_NBN_OutputLane.result,good,NFY_NBN_OutputLane.first]
  · simp [lane,good,NFY_NBN_OutputLane.result]

#print axioms first_source
#print axioms lane_source
end NFY_NBN_FirstByteDependency
-- END copied NBN_FirstByteDependency
-- BEGIN copied NBN_WordArrayEq: lean/NBN_WordArrayEq.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NBN_WordArrayEq
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem list_eq (xs ys : List U32) (hlen : xs.length = ys.length) :
    List.allM (fun (x,y) => do
      let b ← AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x y
      ok (decide (¬ b = true))) (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.allM,pure]
  | cons x xs ih =>
    cases ys with
    | nil => simp_all
    | cons y ys =>
      have tail : xs.length=ys.length := by simpa using hlen
      rw [List.zip_cons_cons]
      simp only [List.allM]
      have eqv : (do let b ← AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x y; ok (decide (¬ b = true))) = ok (decide (x=y)) := by
        simp [AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31,core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
      rw [eqv]
      by_cases same : x=y
      · simp only [same,decide_true,bind_tc_ok,if_pos]
        simpa only [List.cons.injEq, true_and, liftFun2, bind_tc_ok] using ih ys tail
      · simp [same,pure]

theorem source {n : Usize} (a b : Array U32 n) :
    core.array.equality.PartialEqArray.eq AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b = ok (decide (a=b)) := by
  unfold core.array.equality.PartialEqArray.eq
  have length : a.length=b.length := by have := a.property; have := b.property; scalar_tac
  rw [if_pos length, list_eq a.val b.val (by have := a.property; have := b.property; scalar_tac)]
  have eqv : (a.val=b.val) ↔ a=b := by
    cases a
    cases b
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  simp only [eqv]

#print axioms list_eq
#print axioms source
end NFY_NBN_WordArrayEq
-- END copied NBN_WordArrayEq
-- BEGIN copied NBN_ArrayNe: lean/NBN_ArrayNe.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_ArrayNe
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem bytes {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b = ok (decide (a ≠ b)) := by
  simp [core.array.equality.PartialEqArray.ne,NBH_ArrayEq.source]

theorem words {n : Usize} (a b : Array U32 n) :
    core.array.equality.PartialEqArray.ne
      AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b =
      ok (decide (a ≠ b)) := by
  simp [core.array.equality.PartialEqArray.ne,NFY_NBN_WordArrayEq.source]

#print axioms bytes
#print axioms words
end NFY_NBN_ArrayNe
-- END copied NBN_ArrayNe
-- BEGIN copied NBK_StatementPrefix: lean/NBK_StatementPrefix.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBK_StatementPrefix
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1
abbrev zero : Array U8 32#usize := Array.repeat 32#usize 0#u8
abbrev common := NBD_TerminalProjection.common

theorem zero_rejected (s : Statement)
    (h : (common s).master_account = zero ∨
      (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Err .NonZeroBinding) := by
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [NBD_TerminalProjection.source_common]
  simp only [bind_tc_ok, NBH_ArrayEq.source]
  rcases h with h | h | h
  · simp [h]
  · by_cases first : (common s).master_account = zero <;> simp [first,h]
  · by_cases first : (common s).master_account = zero
    · simp [first]
    · by_cases second : (common s).checkpoint_account = zero <;> simp [first,second,h]

theorem lane_rejected (s : Statement)
    (hm : (common s).master_account ≠ zero)
    (hc : (common s).checkpoint_account ≠ zero)
    (hs : (common s).selected_lane_account ≠ zero)
    (lane : 8 ≤ (common s).output_lane.val) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Err .InvalidOutputLane) := by
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [NBD_TerminalProjection.source_common]
  simp only [bind_tc_ok, NBH_ArrayEq.source]
  simp only [hm,hc,hs,decide_false,if_false]
  unfold pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT
  have cast : core.convert.num.FromUsizeU8.from (common s).output_lane =
      Usize.ofNatCore (common s).output_lane.val (by scalar_tac) := by scalar_tac
  simp only [lift,cast,bind_tc_ok]
  have bound : (Usize.ofNatCore (common s).output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
  simp only [bound,if_true]
  rfl

#print axioms zero_rejected
#print axioms lane_rejected
end NFY_NBK_StatementPrefix
-- END copied NBK_StatementPrefix
-- BEGIN copied NBN_StatementResult: lean/NBN_StatementResult.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NBN_StatementResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
attribute [local instance] Classical.propDecidable
abbrev Statement := PoolV1PairForestTerminalStatementV1
abbrev Error := PoolV1PairForestTerminalFormatErrorV1
abbrev PaymentError := pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev common := NBD_TerminalProjection.common
abbrev parts := NBD_TerminalProjection.parts
abbrev zero := NFY_NBK_StatementPrefix.zero

def payment (s : Statement) : Result (core.result.Result (Array U8 216#usize) PaymentError) :=
  match s with
  | .PrivateTransfer _ p => pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p
  | .Withdrawal _ p => pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p

def lateStatus (s : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    core.result.Result Unit pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  if U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
      some s.candidate_afterstate.next_pair_index then .Err .AfterstateIndexMismatch
  else NFY_NBN_LateTail.status s

def suffix (s : Statement) : core.result.Result Unit Error :=
  let c := common s
  let (pool,deployment,sequence,anchor,nullifier,_) := parts s
  if pool ≠ c.master_account then .Err .MasterBindingMismatch
  else if deployment ≠ c.lane_transition.live_snapshot.deployment_domain then .Err .DeploymentBindingMismatch
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then .Err .MasterBindingMismatch
  else if sequence ≠ c.checkpoint_sequence then .Err .CheckpointBindingMismatch
  else if anchor ≠ c.historical_global_anchor then .Err .HistoricalAnchorMismatch
  else match NFY_NBN_OutputLane.result nullifier with
    | .Err e => .Err (.Account e)
    | .Ok lane => if lane ≠ c.output_lane then .Err .OutputLaneMismatch
      else match lateStatus c.lane_transition with
        | .Err e => .Err (.LaneTransition e)
        | .Ok _ => .Ok ()

def result (s : Statement) : Result (core.result.Result Unit Error) :=
  let c := common s
  if c.master_account = zero ∨ c.checkpoint_account = zero ∨ c.selected_lane_account = zero then
    ok (.Err .NonZeroBinding)
  else if 8 ≤ c.output_lane.val then ok (.Err .InvalidOutputLane)
  else do
    let r ← payment s
    match r with
    | .Err e => ok (.Err (.Payment e))
    | .Ok _ => ok (suffix s)

theorem source (s : Statement) : validate_pool_v1_pair_forest_terminal_statement_v1 s = result s := by
  by_cases hm : (common s).master_account = zero
  · rw [NFY_NBK_StatementPrefix.zero_rejected s (Or.inl hm)]
    simp [result,hm]
  · by_cases hc : (common s).checkpoint_account = zero
    · rw [NFY_NBK_StatementPrefix.zero_rejected s (Or.inr (Or.inl hc))]
      simp [result,hc]
    · by_cases hs : (common s).selected_lane_account = zero
      · rw [NFY_NBK_StatementPrefix.zero_rejected s (Or.inr (Or.inr hs))]
        simp [result,hs]
      · by_cases lane : 8 ≤ (common s).output_lane.val
        · rw [NFY_NBK_StatementPrefix.lane_rejected s hm hc hs lane]
          simp [result,hm,hc,hs,lane]
        · unfold validate_pool_v1_pair_forest_terminal_statement_v1
          rw [NBD_TerminalProjection.source_common]
          simp only [NBH_ArrayEq.source,bind_tc_ok,hm,hc,hs,decide_false,if_false]
          have cast : core.convert.num.FromUsizeU8.from (common s).output_lane =
              Usize.ofNatCore (common s).output_lane.val (by scalar_tac) := by scalar_tac
          have small : ¬ (Usize.ofNatCore (common s).output_lane.val (by scalar_tac)) ≥ 8#usize := by scalar_tac
          simp only [lift,cast,bind_tc_ok,pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT,small,if_false]
          unfold result
          simp only [hm,hc,hs,lane,not_false_eq_true,or_self,if_false]
          cases s <;> simp only [payment]
          all_goals apply NFY_NBN_LateFactor.bind_ext
          all_goals intro pay
          all_goals cases pay with
          | Err e => rfl
          | Ok bytes =>
            simp only [core.result.Result.map_err,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTry.branch]
            rw [NBD_TerminalProjection.source_parts]
            simp only [bind_tc_ok,NFY_NBN_ArrayNe.bytes,NFY_NBN_ArrayNe.words,
              NFY_NBN_OutputLane.source]
            simp only [suffix,common,parts,NBD_TerminalProjection.common,NBD_TerminalProjection.parts,
              Aeneas.Std.uncurry,decide_eq_true_eq,bne_iff_ne]
            simp only [Array.to_slice_mut,lift,bind_tc_ok,Aeneas.Std.uncurry,
              NFY_NBN_LateResult.source,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
            simp only [show ¬ ((1520#usize).val ≠ 1520) by decide,if_false]
            simp only [lateStatus]
            repeat' first
              | rfl
              | (split <;> try simp_all only [bind_tc_ok,decide_eq_true_eq,bne_iff_ne])

#print axioms source
end NFY_NBN_StatementResult
-- END copied NBN_StatementResult
-- BEGIN copied NBN_BindingChecks: lean/NBN_BindingChecks.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_BindingChecks
abbrev ErrT := NFY_NBN_StatementResult.Error
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
abbrev Common := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
attribute [local instance] Classical.propDecidable

def chain (c : Common) (p : NBD_TerminalProjection.Parts)
    (tail : core.result.Result Unit ErrT) : core.result.Result Unit ErrT :=
  if p.1 ≠ c.master_account then .Err .MasterBindingMismatch
  else if p.2.1 ≠ c.lane_transition.live_snapshot.deployment_domain then .Err .DeploymentBindingMismatch
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then .Err .MasterBindingMismatch
  else if p.2.2.1 ≠ c.checkpoint_sequence then .Err .CheckpointBindingMismatch
  else if p.2.2.2.1 ≠ c.historical_global_anchor then .Err .HistoricalAnchorMismatch
  else tail

def tail (s : Statement) : core.result.Result Unit ErrT :=
  match NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | .Err e => .Err (.Account e)
  | .Ok lane => if lane ≠ (common s).output_lane then .Err .OutputLaneMismatch
    else match lateStatus (common s).lane_transition with
      | .Err e => .Err (.LaneTransition e)
      | .Ok _ => .Ok ()

theorem factor (s : Statement) : suffix s = chain (common s) (parts s) (tail s) := by
  cases s <;> rfl

theorem fields (c : Common) (p : NBD_TerminalProjection.Parts)
    (t : core.result.Result Unit ErrT) (h : chain c p t = .Ok ()) :
    p.1 = c.master_account ∧ p.2.1 = c.lane_transition.live_snapshot.deployment_domain ∧
    c.lane_transition.live_snapshot.pool = c.master_account ∧
    p.2.2.1 = c.checkpoint_sequence ∧ p.2.2.2.1 = c.historical_global_anchor := by
  unfold chain at h
  by_cases h1 : p.1 = c.master_account
  · simp only [h1,ne_eq,not_true_eq_false,if_false] at h
    by_cases h2 : p.2.1 = c.lane_transition.live_snapshot.deployment_domain
    · simp only [h2,ne_eq,not_true_eq_false,if_false] at h
      by_cases h3 : c.lane_transition.live_snapshot.pool = c.master_account
      · simp only [h3,ne_eq,not_true_eq_false,if_false] at h
        by_cases h4 : p.2.2.1 = c.checkpoint_sequence
        · simp only [h4,ne_eq,not_true_eq_false,if_false] at h
          by_cases h5 : p.2.2.2.1 = c.historical_global_anchor
          · exact ⟨h1,h2,h3,h4,h5⟩
          · simp only [h5,ne_eq,not_false_eq_true,if_true] at h; cases h
        · simp only [h4,ne_eq,not_false_eq_true,if_true] at h; cases h
      · simp only [h3,ne_eq,not_false_eq_true,if_true] at h; cases h
    · simp only [h2,ne_eq,not_false_eq_true,if_true] at h; cases h
  · simp only [h1,ne_eq,not_false_eq_true,if_true] at h; cases h

#print axioms factor
#print axioms fields
end NFY_NBN_BindingChecks
-- END copied NBN_BindingChecks
-- BEGIN copied NBN_StatementCut: lean/NBN_StatementCut.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_StatementCut
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
attribute [local instance] Classical.propDecidable
abbrev PE := pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev AE := pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
abbrev LE := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
abbrev E := NFY_NBN_StatementResult.Error

def tail (s : Statement) (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE) :
    core.result.Result Unit E :=
  match lane with
  | .Err e => .Err (.Account e)
  | .Ok l => if l ≠ (common s).output_lane then .Err .OutputLaneMismatch
    else match late with
      | .Err e => .Err (.LaneTransition e)
      | .Ok _ => .Ok ()

/-- Exact native K003 control cut. Child values are arbitrary, not successful. -/
def run (s : Statement) (pay : Result (core.result.Result (Array U8 216#usize) PE))
    (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE) : Result (core.result.Result Unit E) :=
  if (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero then ok (.Err .NonZeroBinding)
  else if 8 ≤ (common s).output_lane.val then ok (.Err .InvalidOutputLane)
  else do
    let r ← pay
    match r with
    | .Err e => ok (.Err (.Payment e))
    | .Ok _ => ok (NFY_NBN_BindingChecks.chain (common s) (parts s) (tail s lane late))

theorem source (s : Statement) :
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s =
      run s (payment s) (NFY_NBN_OutputLane.result (parts s).2.2.2.2.1)
        (lateStatus (common s).lane_transition) := by
  rw [NFY_NBN_StatementResult.source]
  cases s <;> rfl

/-- Substitution uses only exact lower Results on the SAME input/variant. -/
theorem lower_substitution (s : Statement)
    (pay : Result (core.result.Result (Array U8 216#usize) PE))
    (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE)
    (payment_exact : pay = payment s)
    (lane_exact : lane = NFY_NBN_OutputLane.result (parts s).2.2.2.2.1)
    (late_exact : late = lateStatus (common s).lane_transition) :
    run s pay lane late =
      pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s := by
  rw [payment_exact,lane_exact,late_exact,source]

#print axioms source
#print axioms lower_substitution
end NFY_NBN_StatementCut
-- END copied NBN_StatementCut
-- BEGIN copied NBN_ValidatorSummary: lean/NBN_ValidatorSummary.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NBN_ValidatorSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
attribute [local instance] Classical.propDecidable
abbrev E := NFY_NBN_StatementResult.Error
abbrev Transfer := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev PaymentResult := Result (core.result.Result (Array U8 216#usize) PaymentError)
abbrev Encode := NFY_NBN_EncoderSummary.Encode

def NBN_Dep_TransferEncode (f : Transfer → PaymentResult) : Prop :=
  ∀ p, f p = pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p

def NBN_Dep_WithdrawalEncode (f : Withdrawal → PaymentResult) : Prop :=
  ∀ p, f p = pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p

def paymentWith (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult) : Statement → PaymentResult
  | .PrivateTransfer _ p => t p
  | .Withdrawal _ p => w p

theorem payment_source (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (ht : NBN_Dep_TransferEncode t) (hw : NBN_Dep_WithdrawalEncode w) (s : Statement) :
    paymentWith t w s = payment s := by
  cases s <;> first | exact ht _ | exact hw _

def chain (c : NFY_NBN_BindingChecks.Common) (p : NBD_TerminalProjection.Parts)
    (tail : Result (core.result.Result Unit E)) : Result (core.result.Result Unit E) :=
  if p.1 ≠ c.master_account then ok (.Err .MasterBindingMismatch)
  else if p.2.1 ≠ c.lane_transition.live_snapshot.deployment_domain then ok (.Err .DeploymentBindingMismatch)
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then ok (.Err .MasterBindingMismatch)
  else if p.2.2.1 ≠ c.checkpoint_sequence then ok (.Err .CheckpointBindingMismatch)
  else if p.2.2.2.1 ≠ c.historical_global_anchor then ok (.Err .HistoricalAnchorMismatch)
  else tail

theorem chain_pure (c : NFY_NBN_BindingChecks.Common) (p : NBD_TerminalProjection.Parts)
    (tail : core.result.Result Unit E) :
    chain c p (ok tail) = ok (NFY_NBN_BindingChecks.chain c p tail) := by
  unfold chain NFY_NBN_BindingChecks.chain
  repeat' first | rfl | split

def tail (enc : Encode) (s : Statement) : Result (core.result.Result Unit E) := do
  let lane ← NFY_NBN_FirstByteDependency.lane enc (parts s).2.2.2.2.1
  match lane with
  | .Err e => ok (.Err (.Account e))
  | .Ok l =>
    if l ≠ (common s).output_lane then ok (.Err .OutputLaneMismatch)
    else do
      let (r,_) ← NFY_NBN_LateSummary.run enc (common s).lane_transition NFY_NBN_LateResult.zero
      match r with
      | .Err e => ok (.Err (.LaneTransition e))
      | .Ok _ => ok (.Ok ())

theorem tail_source (enc : Encode)
    (lower : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc) (s : Statement) :
    tail enc s = ok (NFY_NBN_BindingChecks.tail s) := by
  unfold tail
  rw [NFY_NBN_FirstByteDependency.lane_source enc lower,NFY_NBN_OutputLane.source]
  simp only [bind_tc_ok]
  unfold NFY_NBN_BindingChecks.tail
  cases lane : NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | Err e => rfl
  | Ok l =>
    by_cases mismatch : l = (common s).output_lane
    · simp only [mismatch,ne_eq,not_true_eq_false,if_false]
      rw [NFY_NBN_LateSummary.source enc lower,NFY_NBN_LateResult.source]
      have len : NFY_NBN_LateResult.zero.length = 1520 := by
        simp only [NFY_NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
        rfl
      rw [if_neg (not_not.mpr len)]
      unfold lateStatus
      by_cases index : U64.checked_add (common s).lane_transition.live_snapshot.next_pair_index 1#u64 ≠
          some (common s).lane_transition.candidate_afterstate.next_pair_index
      · simp only [ne_eq] at index
        simp only [ne_eq,index,not_false_eq_true,if_true,bind_tc_ok]
        rfl
      · simp only [index,if_false,bind_tc_ok,Aeneas.Std.uncurry]
        cases NFY_NBN_LateTail.status (common s).lane_transition <;> rfl
    · simp only [mismatch,ne_eq,not_false_eq_true,if_true]

def run (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult) (s : Statement) :
    Result (core.result.Result Unit E) :=
  if (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero then ok (.Err .NonZeroBinding)
  else if 8 ≤ (common s).output_lane.val then ok (.Err .InvalidOutputLane)
  else do
    let pay ← paymentWith t w s
    match pay with
    | .Err e => ok (.Err (.Payment e))
    | .Ok _ => chain (common s) (parts s) (tail enc s)

theorem source (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (hd : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc)
    (ht : NBN_Dep_TransferEncode t) (hw : NBN_Dep_WithdrawalEncode w) (s : Statement) :
    run enc t w s = pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s := by
  rw [NFY_NBN_StatementResult.source]
  unfold run result
  dsimp only
  rw [payment_source t w ht hw s,tail_source enc hd s,chain_pure,← NFY_NBN_BindingChecks.factor s]
  rfl

#print axioms payment_source
#print axioms chain_pure
#print axioms tail_source
#print axioms source
end NFY_NBN_ValidatorSummary
-- END copied NBN_ValidatorSummary
-- BEGIN copied NBN_StatementDomains: lean/NBN_StatementDomains.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NBN_StatementDomains
open Aeneas Aeneas.Std Result
open NFY_NBN_StatementResult
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

/-- Same-variant child, not an independently selected successful payment. -/
theorem payment_reached (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    ∃ bytes, payment s = ok (.Ok bytes) ∧ suffix s = .Ok () := by
  rw [source] at accepted
  unfold result at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · cases hp : payment s with
      | fail e => simp only [hp,bind_tc_fail] at accepted; cases accepted
      | div => simp only [hp,bind_tc_div] at accepted; cases accepted
      | ok r =>
        simp only [hp,bind_tc_ok] at accepted
        cases r with
        | Err e => cases accepted
        | Ok bytes => exact ⟨bytes,rfl,Result.ok.inj accepted⟩

theorem bindings (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    (parts s).1 = (common s).master_account ∧
    (parts s).2.1 = (common s).lane_transition.live_snapshot.deployment_domain ∧
    (common s).lane_transition.live_snapshot.pool = (common s).master_account ∧
    (parts s).2.2.1 = (common s).checkpoint_sequence ∧
    (parts s).2.2.2.1 = (common s).historical_global_anchor := by
  obtain ⟨_,_,h⟩ := payment_reached s accepted
  rw [NFY_NBN_BindingChecks.factor] at h
  exact NFY_NBN_BindingChecks.fields (common s) (parts s) (NFY_NBN_BindingChecks.tail s) h

theorem lane_late (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 = .Ok (common s).output_lane ∧
    lateStatus (common s).lane_transition = .Ok () := by
  obtain ⟨_,_,h⟩ := payment_reached s accepted
  obtain ⟨hp,hd,hl,hs,ha⟩ := bindings s accepted
  simp only [suffix,hp,hd,hl,hs,ha,ne_eq,not_true_eq_false,if_false] at h
  cases lane : NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | Err e => simp only [lane] at h; cases h
  | Ok value =>
    simp only [lane] at h
    split at h
    · cases h
    · rename_i same
      have eq : value = (common s).output_lane := not_not.mp same
      subst value
      refine ⟨rfl,?_⟩
      cases late : lateStatus (common s).lane_transition with
      | Err e => simp only [late] at h; cases h
      | Ok u => cases u; rfl

theorem late_children (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    U64.checked_add (common s).lane_transition.live_snapshot.next_pair_index 1#u64 =
      some (common s).lane_transition.candidate_afterstate.next_pair_index ∧
    NFY_NBH_LiveValidator.result (common s).lane_transition.live_snapshot = .Ok () ∧
    NFY_NBH_Validators.afterResult (common s).lane_transition.candidate_afterstate = .Ok () := by
  have h := (lane_late s accepted).2
  unfold lateStatus at h
  split at h
  · cases h
  · rename_i index
    refine ⟨not_not.mp index,?_⟩
    unfold NFY_NBN_LateTail.status at h
    cases live : NFY_NBH_LiveValidator.result (common s).lane_transition.live_snapshot with
    | Err e => simp only [live] at h; cases h
    | Ok u =>
      cases u
      simp only [live] at h
      refine ⟨rfl,?_⟩
      cases after : NFY_NBH_Validators.afterResult (common s).lane_transition.candidate_afterstate with
      | Err e => simp only [after] at h; cases h
      | Ok u => cases u; rfl

#print axioms payment_reached
#print axioms bindings
#print axioms lane_late
#print axioms late_children
end NFY_NBN_StatementDomains
-- END copied NBN_StatementDomains

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
