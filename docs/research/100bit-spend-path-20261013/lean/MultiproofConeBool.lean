import Aeneas

set_option autoImplicit false
namespace AspisR1.MultiproofConeBool
open Aeneas Aeneas.Std Result

theorem result_if_conj (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (ok (decide q) : Result Bool) else ok false) = ok (decide (p ∧ q)) := by
  by_cases hp : p <;> simp [hp]

theorem result_decide_congr {p q : Prop} [Decidable p] [Decidable q] (same : p ↔ q) :
    (ok (decide p) : Result Bool) = ok (decide q) := by
  have eq : p = q := propext same
  cases eq
  exact congrArg (fun d : Decidable p => ok (@decide p d)) (Subsingleton.elim _ _)

#print axioms result_if_conj
#print axioms result_decide_congr
end AspisR1.MultiproofConeBool
