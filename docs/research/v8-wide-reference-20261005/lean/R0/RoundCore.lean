import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! Shared, field-generic formulas. This module can be imported by both the
Wide and V8 environments without their incompatible natural-basis modules. -/
set_option autoImplicit false
namespace AspisR0.RoundCore
open Polynomial
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

def slot (d : Fin 256) (s : Fin 4) : Fin 1024 := ⟨4*d.val+s.val, by omega⟩
def unflatten (q : Fin 1024 → K) (i : Fin 256 × Fin 4) : K := q (slot i.1 i.2)
def quarter : K := (4 : K)⁻¹
def fold (alpha : K) (q : Fin 1024 → K) (d : Fin 256) : K :=
  ∑ s : Fin 4, q (slot d s) * alpha ^ s.val
def dualFold (alpha : K) (w : Fin 1024 → K) (d : Fin 256) : K :=
  ∑ t : Fin 4, w (slot d t) * alpha ^ ((4-t.val)%4)
def polynomial (q w : Fin 1024 → K) : K[X] :=
  ∑ d : Fin 256, ∑ s : Fin 4, ∑ t : Fin 4,
    monomial (s.val+(4-t.val)%4) (quarter*q (slot d s)*w (slot d t))

theorem eval_polynomial (alpha : K) (q w : Fin 1024 → K) :
    (polynomial q w).eval alpha =
      quarter * ∑ d, fold alpha q d * dualFold alpha w d := by
  simp only [polynomial, eval_finsetSum, eval_monomial, fold, dualFold,
    Finset.mul_sum, Finset.sum_mul, pow_add]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

#print axioms eval_polynomial
end
end AspisR0.RoundCore
