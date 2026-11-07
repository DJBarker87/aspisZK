import NNG_EmittedContext
import RSL_Base
set_option autoImplicit false
namespace AspisR1.NNG_TraceAlgebra
open Aeneas Aeneas.Std Result NMT_CallTree

theorem erase_bindM {A B : Type} (code : Code A) (k : A → Code B) :
    erase (code >>= k) = (erase code >>= fun a => erase (k a)) := erase_bind code k

theorem erase_pureM {A : Type} (a : A) : erase (pure a : Code A) = .ok a := rfl

theorem erase_liftM {A : Type} (r : Result A) : erase (liftM r : Code A) = r := erase_lift r

theorem erase_lift {A : Type} (r : Result A) :
    erase (monadLift r : Code A) = r := NMT_CallTree.erase_lift r

/-- Small symbolic congruence, rather than reduction of a concrete parent. -/
theorem erase_control {B C A : Type} (cf : core.ops.control_flow.ControlFlow B C)
    (onContinue : C → Code A) (onBreak : B → Code A) :
    erase (match cf with
      | .Continue a => onContinue a
      | .Break b => onBreak b) =
    match cf with
      | .Continue a => erase (onContinue a)
      | .Break b => erase (onBreak b) := by
  cases cf <;> rfl

theorem erase_if {A : Type} (p : Prop) [Decidable p] (a b : Code A) :
    erase (if p then a else b) = if p then erase a else erase b := by
  by_cases h : p
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

#print axioms erase_bindM
#print axioms erase_pureM
#print axioms erase_liftM
#print axioms erase_lift
#print axioms erase_control
#print axioms erase_if
end AspisR1.NNG_TraceAlgebra
