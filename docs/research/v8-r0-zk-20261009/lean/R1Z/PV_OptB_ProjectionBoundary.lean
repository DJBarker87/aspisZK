import R1Z.ProverCommitSemanticTransport26
set_option autoImplicit false
namespace R1Z.PV_OptB_ProjectionBoundary
open Aeneas Aeneas.Std Result ProverCommitSemanticTransport26

/-- Small interface diagnostic, not an admitted native counterexample.
The source-body map can forget a state coordinate. Equal projected source
results alone then cannot certify a complete OS observation. -/
theorem erased_state_equal :
    mapR (fun _ : Bool => ()) (.ok false) = mapR (fun _ : Bool => ()) (.ok true) := rfl

#print axioms erased_state_equal
theorem full_state_differs : (Result.ok false : Result Bool) ≠ Result.ok true := by
  intro same
  cases same

#print axioms full_state_differs
theorem observation_factor_sufficient {S T E : Type}
    (project : S → T) (observe : S → E) (decode : T → E)
    (factor : ∀ s, observe s = decode (project s)) (s t : S)
    (same : project s = project t) : observe s = observe t := by
  rw [factor s,factor t,same]

#print axioms observation_factor_sufficient
theorem mapR_compose {S T E : Type} (project : S → T) (decode : T → E) (r : Result S) :
    mapR decode (mapR project r) = mapR (fun s => decode (project s)) r := by
  cases r <;> rfl

#print axioms mapR_compose
theorem projected_observation_sufficient {S T E : Type}
    (project : S → T) (observe : S → E) (decode : T → E)
    (factor : ∀ s, observe s = decode (project s)) (left right : Result S)
    (same : mapR project left = mapR project right) : mapR observe left = mapR observe right := by
  have factor_eq : observe = fun s => decode (project s) := funext factor
  rw [factor_eq, ← mapR_compose project decode left, ← mapR_compose project decode right, same]

#print axioms projected_observation_sufficient
end R1Z.PV_OptB_ProjectionBoundary
