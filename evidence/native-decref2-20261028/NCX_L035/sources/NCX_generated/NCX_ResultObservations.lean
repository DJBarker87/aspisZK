import NCX_Observations
set_option autoImplicit false
namespace NCX_ResultObservations
open Aeneas Aeneas.Std Result
inductive Observation where
  | success : NCX_Observations.Observation → Observation
  | error : NCX_Reference.PoolV1VerifierRegistryFormatError → Observation

def registry (r : core.result.Result NCX_Reference.VerifierRegistryV2
    NCX_Reference.PoolV1VerifierRegistryFormatError) (field j : Nat) : Observation :=
  match r with
  | .Ok v => .success (NCX_Observations.registry v field j)
  | .Err e => .error e
def entry (r : core.result.Result NCX_Reference.VerifierRegistryEntryV2
    NCX_Reference.PoolV1VerifierRegistryFormatError) (field j : Nat) : Observation :=
  match r with
  | .Ok v => .success (NCX_Observations.entry v field j)
  | .Err e => .error e

theorem registry_injective (a b : core.result.Result NCX_Reference.VerifierRegistryV2
    NCX_Reference.PoolV1VerifierRegistryFormatError)
    (same : ∀ f j, f<12 → j<32 → registry a f j=registry b f j) : a=b := by
  cases a with
  | Ok a =>
    cases b with
    | Ok b =>
      congr 1
      apply NCX_Observations.registry_injective
      intro f j hf hj
      exact Observation.success.inj (same f j hf hj)
    | Err e => cases same 0 0 (by omega) (by omega)
  | Err e =>
    cases b with
    | Ok b => cases same 0 0 (by omega) (by omega)
    | Err d => exact congrArg core.result.Result.Err (Observation.error.inj (same 0 0 (by omega) (by omega)))
theorem entry_injective (a b : core.result.Result NCX_Reference.VerifierRegistryEntryV2
    NCX_Reference.PoolV1VerifierRegistryFormatError)
    (same : ∀ f j, f<15 → j<32 → entry a f j=entry b f j) : a=b := by
  cases a with
  | Ok a =>
    cases b with
    | Ok b =>
      congr 1
      apply NCX_Observations.entry_injective
      intro f j hf hj
      exact Observation.success.inj (same f j hf hj)
    | Err e => cases same 0 0 (by omega) (by omega)
  | Err e =>
    cases b with
    | Ok b => cases same 0 0 (by omega) (by omega)
    | Err d => exact congrArg core.result.Result.Err (Observation.error.inj (same 0 0 (by omega) (by omega)))
#print axioms registry_injective
#print axioms entry_injective
end NCX_ResultObservations
