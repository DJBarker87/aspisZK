import R1Z.ProverRwP6ArrayRead
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6ArrayMutRead
open Aeneas Aeneas.Std Result
theorem read {α : Type} {n : Usize} (v : Array α n) (i : Usize)
    (bound : i.val < n.val) : ∃ x back, Array.index_mut_usize v i = ok (x,back) := by
  obtain ⟨x,hx⟩ := ProverRwP6ArrayRead.read v i bound
  unfold Array.index_mut_usize
  rw [hx]
  exact ⟨x,_,rfl⟩
#print axioms read
end R1Z.ProverRwP6ArrayMutRead
