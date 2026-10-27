import R1Z.PV_CB_CanonicalArrays
import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_CB_ProducerPost
open Aeneas Aeneas.Std Result
/-- A postcondition on successful inner results; all rejection and divergence
    cases remain in the exact extracted Result. -/
def Good {A E : Type} (valid : A → Prop) (run : Result (core.result.Result A E)) : Prop :=
  ∀ value, run = ok (.Ok value) → valid value

theorem pure {A E : Type} (valid : A → Prop) (value : A) (h : valid value) :
    Good valid (ok (.Ok value) : Result (core.result.Result A E)) := by
  intro out eq
  cases eq
  exact h

theorem error {A E : Type} (valid : A → Prop) (err : E) :
    Good valid (ok (.Err err) : Result (core.result.Result A E)) := by
  intro out eq
  cases eq
#print axioms pure
#print axioms error
end R1Z.PV_CB_ProducerPost
