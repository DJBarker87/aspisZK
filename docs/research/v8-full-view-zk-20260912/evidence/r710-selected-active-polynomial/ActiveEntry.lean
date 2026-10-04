import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import AspisV8R17.WeightedScatter

/-! Polynomial normal form for the direct active map. The six constants
are the fixed linear transport/chord basis coefficients. Their source
instantiation is separate from this universal degree theorem. -/
set_option autoImplicit false
namespace AspisV8R17
noncomputable section
open MvPolynomial
variable {F : Type*} [CommRing F] [Nontrivial F]
abbrev ActivePoly (F : Type*) [CommRing F] := MvPolynomial (Fin 3) F

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

def activeAssignment (alpha u v : F) (j : Fin 3) : F :=
  if j=0 then alpha else if j=1 then u else v

theorem activeEntry_eval (a b : Fin 3 → F) (k : ℕ) (alpha u v : F) :
    eval (activeAssignment alpha u v) (activeEntry a b k) =
      (1+u*v)*(a 0-alpha^k*b 0) + (u*v-1)*(a 1-alpha^k*b 1) +
        (-(u+v))*(a 2-alpha^k*b 2) := by
  simp [activeEntry, activeChord, activeAssignment, Fin.sum_univ_succ]
  ring

def sourceBasisConstants (half : F) (q : ℕ → F) (r : ℕ) (j : Fin 3) : F :=
  if j=0 then sourceChord half q 1 0 0 r
  else if j=1 then sourceChord half q 0 1 0 r
  else sourceChord half q 0 0 1 r

theorem sourceEntry_eval (half : F) (q s : ℕ → F) (r k : ℕ) (alpha u v : F) :
    eval (activeAssignment alpha u v)
      (activeEntry (sourceBasisConstants half q r) (sourceBasisConstants half s r) k) =
    sourceChord half (fun i => q i-alpha^k*s i) (1+u*v) (u*v-1) (-(u+v)) r := by
  rw [activeEntry_eval]
  simpa [sourceBasisConstants] using
    (sourceChord_six_constants half q s (1+u*v) (u*v-1) (-(u+v)) (alpha^k) r).symm

theorem sourceEntry_degree (half : F) (q s : ℕ → F) (r k : ℕ) (hk : k≤3) :
    (activeEntry (sourceBasisConstants half q r) (sourceBasisConstants half s r) k).totalDegree ≤ 5 :=
  activeEntry_degree _ _ k hk

#print axioms sourceEntry_eval
#print axioms sourceEntry_degree
#print axioms activeEntry_eval
#print axioms activeChord_degree
#print axioms activeEntry_degree
end
end AspisV8R17
