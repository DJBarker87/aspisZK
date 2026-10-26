import RPz7_F3K_ArrayFacts
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.F3K_ArrayValues

theorem updated {α : Type} {n : Usize} (a b : Array α n) (i : Usize) (x : α)
    (h : Array.update a i x=ok b) : b=Aeneas.Std.Array.set a i x := by
  unfold Array.update at h
  split at h
  · cases h
  · exact (Result.ok.inj h).symm

theorem mutated {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (old : α) (put : α → Array α n)
    (h : Array.index_mut_usize a i=ok (old,put)) : put=Aeneas.Std.Array.set a i := by
  unfold Array.index_mut_usize Array.index_usize at h
  split at h
  · cases h
  · simp only [bind_tc_ok] at h
    exact (congrArg Prod.snd (Result.ok.inj h)).symm

#print axioms updated
#print axioms mutated
end AspisR1.F3K_ArrayValues
