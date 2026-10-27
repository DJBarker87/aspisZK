import Tx2N_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Reserved
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Ops

theorem loop_zeros (fuel : Nat) (s : Slice U8) (i : Nat) (rest : core.slice.iter.Iter U8)
    (enough : s.val.length - i ≤ fuel)
    (scan : headerLoop fuel ⟨s,i⟩ = ok (false,rest)) :
    ∀ j (hj : j < s.val.length), i ≤ j → s.val[j] = 0#u8 := by
  induction fuel generalizing i with
  | zero => intro j hj lo; omega
  | succ fuel ih =>
    intro j hj lo
    have room : i < s.val.length := by omega
    have next : core.slice.iter.IteratorSliceIter.next ⟨s,i⟩ =
        ok (some (s.val[i]'room),⟨s,i+1⟩) := by
      simp only [core.slice.iter.IteratorSliceIter.next]
      have active : i < (Slice.len s).val := room
      rw [dif_pos active]
      rfl
    rw [headerLoop,next,bind_tc_ok] at scan
    change (if (s.val[i]'room != 0#u8) then ok (true,⟨s,i+1⟩) else
      headerLoop fuel ⟨s,i+1⟩) = ok (false,rest) at scan
    have zero : s.val[i] = 0#u8 := by
      by_contra nz
      have bit : (s.val[i]'room != 0#u8) = true := by simpa only [bne_iff_ne] using nz
      simp only [bit,ite_true] at scan
      cases scan
    simp only [zero,bne_self_eq_false,Bool.false_eq_true,ite_false] at scan
    by_cases same : j = i
    · subst j; exact zero
    · exact ih (i+1) (by omega) scan j hj (by omega)

theorem zeros (s : Slice U8) (rest : core.slice.iter.Iter U8)
    (size : s.val.length = 5)
    (scan : headerAny ⟨s,0⟩ = ok (false,rest)) : s.val = List.replicate 5 0#u8 := by
  have values := loop_zeros (s.val.length+1) s 0 rest (by omega) scan
  apply List.ext_getElem
  · simp [size]
  · intro j hj hk
    rw [List.getElem_replicate]
    exact values j hj (Nat.zero_le _)

#print axioms loop_zeros
#print axioms zeros
end AspisR1.Tx2N_Reserved
end
