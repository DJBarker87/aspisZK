import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Exact list-level semantics of the two R1 semantic polynomial primitives.
The current r1_semantic cost-probe source folds the 28 decoded coefficients
from seed coefficient 0 for the endpoint boundary and uses reverse Horner for
the challenge value. This module isolates those algebraic identities from the
unproved extraction/boundary adapter. -/
set_option autoImplicit false

namespace AspisR1PublicPreparation.RawSemanticPolynomialOps

variable {K : Type} [CommSemiring K]

noncomputable def polynomial : List K → Polynomial K
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * polynomial cs

def sourceBoundary (seed : K) (cs : List K) : K :=
  cs.foldl (fun acc c => acc + c) seed

def sourceValue (x : K) (cs : List K) : K :=
  cs.reverse.foldl (fun acc c => acc * x + c) 0

def lowHorner (x : K) : List K → K
  | [] => 0
  | c :: cs => c + x * lowHorner x cs

theorem sourceBoundary_eq_seed_add_sum (seed : K) (cs : List K) :
    sourceBoundary seed cs = seed + cs.sum := by
  induction cs generalizing seed with
  | nil => simp [sourceBoundary]
  | cons c cs ih =>
      change sourceBoundary (seed + c) cs = seed + (c + cs.sum)
      rw [ih]
      simp [add_assoc]

theorem polynomial_eval_eq_lowHorner (x : K) (cs : List K) :
    (polynomial cs).eval x = lowHorner x cs := by
  induction cs with
  | nil => simp [polynomial, lowHorner]
  | cons c cs ih =>
      simp only [polynomial, lowHorner, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X]
      rw [ih]

theorem sourceValue_eq_lowHorner (x : K) (cs : List K) :
    sourceValue x cs = lowHorner x cs := by
  induction cs with
  | nil => simp [sourceValue, lowHorner]
  | cons c cs ih =>
      simp only [sourceValue, List.reverse_cons, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      change (sourceValue x cs) * x + c = c + x * lowHorner x cs
      rw [ih]
      calc
        lowHorner x cs * x + c = x * lowHorner x cs + c := by rw [mul_comm]
        _ = c + x * lowHorner x cs := add_comm _ _

theorem sourceValue_eq_polynomial_eval (x : K) (cs : List K) :
    sourceValue x cs = (polynomial cs).eval x := by
  rw [sourceValue_eq_lowHorner, ← polynomial_eval_eq_lowHorner]

theorem polynomial_eval_zero (cs : List K) :
    (polynomial cs).eval 0 = cs.headD 0 := by
  cases cs with
  | nil => simp [polynomial]
  | cons c cs => simp [polynomial]

theorem polynomial_eval_one (cs : List K) :
    (polynomial cs).eval 1 = cs.sum := by
  induction cs with
  | nil => simp [polynomial]
  | cons c cs ih =>
      simp only [polynomial, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X, ih]
      simp [add_comm, add_left_comm, add_assoc]

theorem sourceBoundary_eq_endpoint_sum (cs : List K) :
    sourceBoundary (cs.headD 0) cs =
      (polynomial cs).eval 0 + (polynomial cs).eval 1 := by
  rw [sourceBoundary_eq_seed_add_sum, polynomial_eval_zero, polynomial_eval_one]

#print axioms sourceBoundary_eq_endpoint_sum
#print axioms sourceValue_eq_polynomial_eval

end AspisR1PublicPreparation.RawSemanticPolynomialOps
