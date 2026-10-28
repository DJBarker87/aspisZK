import R1Z.PV_RunJoin_FlattenTrace30
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SliceTrace30
open Aeneas Aeneas.Std Result BuilderStdModels
variable {T : Type}

theorem drop_cons (xs : List T) (i : Nat) (h : i < xs.length) :
    xs.drop i = xs[i] :: xs.drop (i+1) := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i (Nat.lt_of_succ_lt_succ h)
#print axioms drop_cons

theorem drop_nil (xs : List T) (i : Nat) (h : xs.length ≤ i) : xs.drop i = [] := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => simp at h
    | succ i => exact ih i (Nat.le_of_succ_le_succ h)
#print axioms drop_nil

theorem slice_trace (s : Slice T) (i : Nat) :
    FiniteTrace (core.iter.traits.iterator.IteratorSliceIter T) ⟨s,i⟩ (s.val.drop i) := by
  generalize he : s.val.length-i = remaining
  induction remaining using Nat.strong_induction_on generalizing i with
  | h remaining ih =>
    by_cases hi : i < s.val.length
    · rw [drop_cons s.val i hi]
      apply FiniteTrace.step ⟨s,i⟩ ⟨s,i+1⟩ s.val[i] (s.val.drop (i+1))
      · change core.slice.iter.IteratorSliceIter.next ⟨s,i⟩ = _
        simp only [core.slice.iter.IteratorSliceIter.next,Slice.len_val]
        rw [dif_pos hi]
        rfl
      · exact ih (s.val.length-(i+1)) (by omega) (i+1) rfl
    · rw [drop_nil s.val i (by omega)]
      apply FiniteTrace.done ⟨s,i⟩ ⟨s,i⟩
      change core.slice.iter.IteratorSliceIter.next ⟨s,i⟩ = _
      simp only [core.slice.iter.IteratorSliceIter.next,Slice.len_val]
      rw [dif_neg hi]
#print axioms slice_trace

theorem array_trace {n : Usize} (a : Array T n) :
    FiniteTrace (core.iter.traits.iterator.IteratorSliceIter T) ⟨Array.to_slice a,0⟩ a.val := by
  simpa only [Array.to_slice,List.drop_zero] using slice_trace (Array.to_slice a) 0
#print axioms array_trace
end R1Z.PV_RunJoin_SliceTrace30
