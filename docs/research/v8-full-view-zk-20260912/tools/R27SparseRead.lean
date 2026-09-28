import Lean.Elab.Tactic.Omega

namespace R27SparseRead
universe u
variable {K : Type u}
def entry (mul add : K → K → K) (f : Nat → K) (j : Nat) : K :=
  add (mul (f (j%16)) (f (16+j/16)))
      (mul (f (80+j%16)) (f (96+j/16)))

theorem support_group (j : Nat) (h : j≤478 ∨ j=1023) :
    j/16<30 ∨ j/16=63 := by omega

theorem entry_agrees (mul add : K → K → K) (f g : Nat → K)
    (low : ∀ k, k<16 → f k=g k ∧ f (80+k)=g (80+k))
    (high : ∀ k, k<30 ∨ k=63 → f (16+k)=g (16+k) ∧ f (96+k)=g (96+k))
    (j : Nat) (hj : j≤478 ∨ j=1023) : entry mul add f j = entry mul add g j := by
  have hl := low (j%16) (Nat.mod_lt j (by decide))
  have hh := high (j/16) (support_group j hj)
  simp only [entry, hl.1, hl.2, hh.1, hh.2]

#print axioms support_group
#print axioms entry_agrees
end R27SparseRead
