import NBN_LateFactor
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NBN_LateResult
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
          NBN_LatePrepare.run filled (NBN_LateTail.run s)) := by
  have len : Slice.len output = 1520#usize := by scalar_tac
  simp only [encode_pool_v1_pair_late_public_statement_v1,
    AspisR1.JFs_LateConstants.size,bind_tc_ok,len,bne_self_eq_false,if_false,
    lift,NBK_LatePreflight.option_ne,index,ne_eq,not_true_eq_false,decide_false]
  have tail_eq : NBN_LateFactor.raw s = NBN_LateTail.run s :=
    funext (NBN_LateFactor.raw_eq s)
  rw [← tail_eq]
  rfl

def zero : Slice U8 := (Array.repeat 1520#usize 0#u8).to_slice
def header : Slice U8 := NBN_LatePrepare.value zero

theorem header_length : header.length = 1520 := by
  simp only [header,NBN_LatePrepare.value,Slice.length,zero,Array.to_slice,
    Array.repeat_val,List.length_setSlice!,List.length_set,List.length_replicate]
  rfl

theorem source (s : Statement) (output : Slice U8) :
    encode_pool_v1_pair_late_public_statement_v1 s output =
      if output.length ≠ 1520 then ok (.Err .WrongLength,output)
      else if U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
          some s.candidate_afterstate.next_pair_index then
        ok (.Err .AfterstateIndexMismatch,output)
      else ok (NBN_LateTail.status s,NBN_LateTail.value s header) := by
  by_cases size : output.length = 1520
  · rw [if_neg (not_not.mpr size)]
    by_cases index : U64.checked_add s.live_snapshot.next_pair_index 1#u64 =
      some s.candidate_afterstate.next_pair_index
    · rw [if_neg (not_not.mpr index),factor s output size index,NBK_Fill.source]
      have filled : NBK_Fill.value output 0#u8 = zero := by
        apply Subtype.ext
        change List.replicate output.length 0#u8 = List.replicate 1520 0#u8
        rw [size]
      rw [filled]
      simp only [bind_tc_ok]
      rw [NBN_LatePrepare.exact zero (by simp only [zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]; rfl)]
      exact NBN_LateTail.exact s header header_length
    · rw [if_pos index]
      exact NBK_LatePreflight.wrong_index s output size index
  · rw [if_pos size]
    exact NBK_LatePreflight.wrong_length s output size

#print axioms factor
#print axioms header_length
#print axioms source
end NBN_LateResult
