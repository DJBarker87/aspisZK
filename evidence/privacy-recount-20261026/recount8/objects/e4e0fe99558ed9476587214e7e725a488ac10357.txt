import R1Z.BuilderStdCollect
import R1Z.BuilderRecordsArray

/-! Order-preserving Slice iterator collection by symbolic suffix induction. -/
set_option autoImplicit false
namespace R1Z.BuilderSliceCollect
open Aeneas Aeneas.Std Result BuilderStdModels

variable {T : Type}

theorem slice_trace (s : Slice T) (i : Nat) :
    FiniteTrace (core.iter.traits.iterator.IteratorSliceIter T)
      ⟨s,i⟩ (s.val.drop i) := by
  generalize he : s.val.length-i = remaining
  induction remaining using Nat.strong_induction_on generalizing i with
  | h remaining ih =>
    by_cases hi : i < s.val.length
    · rw [List.drop_eq_getElem_cons hi]
      apply FiniteTrace.step _ ⟨s,i+1⟩
      · change core.slice.iter.IteratorSliceIter.next ⟨s,i⟩ = _
        unfold core.slice.iter.IteratorSliceIter.next
        simp only [Slice.len_val]
        rw [dif_pos hi]
        rfl
      · exact ih (s.val.length-(i+1)) (by omega) (i+1) rfl
    · rw [List.drop_eq_nil_of_le (by omega)]
      apply FiniteTrace.done _ ⟨s,i⟩
      change core.slice.iter.IteratorSliceIter.next ⟨s,i⟩ = _
      unfold core.slice.iter.IteratorSliceIter.next
      simp only [Slice.len_val]
      rw [dif_neg hi]

def suffix (s : Slice T) (i : Nat) : alloc.vec.Vec T :=
  ⟨s.val.drop i,by simpa only [List.length_drop] using (Nat.sub_le s.val.length i).trans s.property⟩

theorem collect_identity {C : Type}
    (f : core.ops.function.FnMut C T T)
    (hf : ∀ c x, f.call_mut c x = ok (x,c))
    (s : Slice T) (i : Nat) (c : C) :
    core.iter.traits.iterator.Iterator.collect.default
      (mappedIterator (core.iter.traits.iterator.IteratorSliceIter T) f)
      (core.iter.traits.collect.FromIteratorVec T) ⟨⟨s,i⟩,c⟩ = ok (suffix s i) := by
  have ht := collect_mapped_trace (core.iter.traits.iterator.IteratorSliceIter T)
    f id hf ⟨s,i⟩ (s.val.drop i) (slice_trace s i) c
  simp only [List.map_id] at ht
  unfold core.iter.traits.iterator.Iterator.collect.default
    core.iter.traits.collect.FromIteratorVec alloc.vec.FromIteratorVec.from_iter
  simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter,bind_tc_ok]
  rw [ht]
  simp only [bind_tc_ok]
  rw [dif_pos (show (s.val.drop i).length ≤ Usize.max from (suffix s i).property)]
  rfl

#print axioms slice_trace
#print axioms collect_identity
end R1Z.BuilderSliceCollect
