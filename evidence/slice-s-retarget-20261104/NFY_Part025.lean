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

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
