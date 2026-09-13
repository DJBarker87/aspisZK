import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace AspisV8R12
variable {K : Type*} [CommRing K]
def prefixWeights : List K → List K
  | [] => [1]
  | x :: xs => (prefixWeights xs).map (fun w => (1-x)*w) ++ (prefixWeights xs).map (fun w => x*w)
theorem sum_scaled (c : K) (xs : List K) : (xs.map (fun x => c*x)).sum = c*xs.sum := by
  induction xs with | nil => simp | cons x xs ih => simp [ih, mul_add]
theorem prefixWeights_sum (xs : List K) : (prefixWeights xs).sum = 1 := by
  induction xs with
  | nil => simp [prefixWeights]
  | cons x xs ih => simp only [prefixWeights, List.sum_append, sum_scaled, ih, mul_one]; ring
theorem symmetrized_response (xs : List K) (q : K) :
    ((prefixWeights xs).map (fun w => q*w)).sum = q := by rw [sum_scaled, prefixWeights_sum, mul_one]
#print axioms prefixWeights_sum
#print axioms symmetrized_response
end AspisV8R12
