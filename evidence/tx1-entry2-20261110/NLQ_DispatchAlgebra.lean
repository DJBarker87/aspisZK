import NLQ_DispatchState
set_option autoImplicit false
namespace NLQ_DispatchAlgebra
open Aeneas Aeneas.Std Result NLQ_DispatchState
/-- Complete primitive Result: failure/divergence retain their attempted event
and do not evaluate the suffix. -/
theorem step_result {A F C X : Type} (world : F) (event : Result X → Event A F C)
 (reply : Result X) (next : X → Run A F C) :
 (step world event reply next).result=(reply >>= fun x => (next x).result) := by
 cases reply <;> rfl
theorem if_result {A F C : Type} (p : Prop) [Decidable p] (yes no : Run A F C) :
 (if p then yes else no).result=if p then yes.result else no.result := by split <;> rfl
theorem step_fail {A F C X : Type} (world : F) (event : Result X → Event A F C)
 (e : Error) (next : X → Run A F C) :
 step world event (.fail e) next = ⟨.fail e,world,[event (.fail e)]⟩ := rfl
theorem step_div {A F C X : Type} (world : F) (event : Result X → Event A F C)
 (next : X → Run A F C) :
 step world event .div next = ⟨.div,world,[event .div]⟩ := rfl
#print axioms step_result
#print axioms if_result
#print axioms step_fail
#print axioms step_div
end NLQ_DispatchAlgebra
