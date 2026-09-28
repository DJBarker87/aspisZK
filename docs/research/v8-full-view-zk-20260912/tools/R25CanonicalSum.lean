import Lean.Elab.Tactic.Omega

namespace R25CanonicalSum
def P : Nat := 2147483647
def addRep (a b : Nat) : Nat := if a+b ≥ P then a+b-P else a+b

theorem sum_bound (a b : Nat) (ha : a<P) (hb : b<P) : a+b<2^32 := by
  simp only [P] at *
  omega

theorem canonical_add (a b : Nat) (ha : a<P) (hb : b<P) :
    addRep a b < P ∧ addRep a b = (a+b)%P := by
  simp only [addRep, P] at *
  split <;> omega

#print axioms sum_bound
#print axioms canonical_add
end R25CanonicalSum
