import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases

/-! Polynomial normal form for the direct active map. The six constants
are the fixed linear transport/chord basis coefficients. Their source
instantiation is separate from this universal degree theorem. -/
set_option autoImplicit false
namespace AspisV8R17
noncomputable section
open MvPolynomial
variable {F : Type*} [Field F]
abbrev ActivePoly (F : Type*) [Field F] := MvPolynomial (Fin 3) F

def activeChord (j : Fin 3) : ActivePoly F :=
  if j=0 then 1 + X 1 * X 2 else if j=1 then X 1 * X 2 - 1 else -(X 1 + X 2)

def activeEntry (a b : Fin 3 → F) (k : ℕ) : ActivePoly F :=
  ∑ j : Fin 3, activeChord j * (C (a j) - X 0 ^ k * C (b j))

theorem activeChord_degree (j : Fin 3) : (activeChord j : ActivePoly F).totalDegree ≤ 2 := by
  have hmul : ((X 1 * X 2 : ActivePoly F)).totalDegree ≤ 2 := by
    simpa using totalDegree_mul (X (1 : Fin 3) : ActivePoly F) (X 2)
  unfold activeChord
  split_ifs
  · exact (totalDegree_add _ _).trans (max_le (by simp) hmul)
  · exact (totalDegree_sub _ _).trans (max_le hmul (by simp))
  · rw [totalDegree_neg]
    exact (totalDegree_add (X (1 : Fin 3) : ActivePoly F) (X 2)).trans (by simp)

theorem activeEntry_degree (a b : Fin 3 → F) (k : ℕ) (hk : k ≤ 3) :
    (activeEntry a b k).totalDegree ≤ 5 := by
  apply totalDegree_finsetSum_le
  intro j _
  have hx : ((X (0 : Fin 3) : ActivePoly F)^k).totalDegree ≤ k := by
    simpa using totalDegree_pow (X (0 : Fin 3) : ActivePoly F) k
  have hb : ((X (0 : Fin 3) : ActivePoly F)^k * C (b j)).totalDegree ≤ 3 := by
    exact (totalDegree_mul _ _).trans (by simpa using hx.trans hk)
  have hs : ((C (a j) : ActivePoly F) - X 0^k * C (b j)).totalDegree ≤ 3 :=
    (totalDegree_sub _ _).trans (max_le (by simp) hb)
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (activeChord_degree j) hs)

#print axioms activeChord_degree
#print axioms activeEntry_degree
end
end AspisV8R17
