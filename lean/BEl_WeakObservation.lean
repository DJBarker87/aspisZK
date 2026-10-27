import BEl_CodeCongr
import BEh_Scope
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_WeakObservation
open Aeneas Aeneas.Std Result SdkC_Source

def accepted {A E : Type} : Option (core.result.Result A E) → Option A
  | some (.Ok a) => some a
  | _ => none

theorem accepted_value {A E : Type} (r : Result (core.result.Result A E)) :
    accepted (BEg_Simulation.value some r) = BEg_Observation.accepted r := by
  cases r with
  | ok value => cases value <;> rfl
  | fail e => rfl
  | div => rfl

/-- Error-insensitive outer equivalence implies the adopted BEh law. This
projection does not assert rejected private-state identity as a requirement. -/
theorem law {S A E : Type} (left right : BEh_Scope.Outcome S A E)
    (same : BEl_CodeCongr.observe left = BEl_CodeCongr.observe right) : BEh_Scope.Law left right := by
  apply BEh_Scope.of_observe
  have projected := congrArg (fun out : Option (core.result.Result A E) × S × Log =>
    (accepted out.1,out.2)) same
  simpa only [BEl_CodeCongr.observe,BEg_Simulation.observation,accepted_value,
    BEg_Observation.observe] using projected

#print axioms accepted_value
#print axioms law
end AspisR1.BEl_WeakObservation
end
