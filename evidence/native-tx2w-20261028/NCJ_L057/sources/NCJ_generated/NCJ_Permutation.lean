import NCJ_CallLog
set_option autoImplicit false
namespace NCJ_Permutation
open Aeneas Aeneas.Std Result

def value (i : Nat) : Nat := match i with | 0=>0 | 1=>3 | 2=>2 | _=>1

theorem source (s : Usize) (h : s.val<4) :
    ∃ i,Array.index_usize FIo_Native.weights.PERM s=ok i ∧ i.val=value s.val ∧ i.val<4 := by
  have cases : s=0#usize ∨ s=1#usize ∨ s=2#usize ∨ s=3#usize := by
    have : s.val=0 ∨ s.val=1 ∨ s.val=2 ∨ s.val=3 := by omega
    rcases this with h|h|h|h
    · exact Or.inl (UScalar.eq_of_val_eq h)
    · exact Or.inr (Or.inl (UScalar.eq_of_val_eq h))
    · exact Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h)))
    · exact Or.inr (Or.inr (Or.inr (UScalar.eq_of_val_eq h)))
  rcases cases with rfl|rfl|rfl|rfl
  · exact ⟨0#usize,by unfold FIo_Native.weights.PERM;rfl,rfl,by decide⟩
  · exact ⟨3#usize,by unfold FIo_Native.weights.PERM;rfl,rfl,by decide⟩
  · exact ⟨2#usize,by unfold FIo_Native.weights.PERM;rfl,rfl,by decide⟩
  · exact ⟨1#usize,by unfold FIo_Native.weights.PERM;rfl,rfl,by decide⟩

#print axioms source
end NCJ_Permutation
