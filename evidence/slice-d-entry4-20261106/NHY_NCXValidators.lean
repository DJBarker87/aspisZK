import NCX_Carrier
import NHY_AllZeroBridge
set_option autoImplicit false
noncomputable section
namespace NHY_NCXValidators
open Aeneas Aeneas.Std Result
open AdapterRw.aspis_statement.pool_v1.verifier_registry

def port (r : core.result.Result Unit NCX_Reference.PoolV1VerifierRegistryFormatError) :
    core.result.Result Unit PoolV1VerifierRegistryFormatError :=
 match r with | .Ok u => .Ok u | .Err e => .Err (NCX_Carrier.error e)

def unport (r : core.result.Result Unit PoolV1VerifierRegistryFormatError) :
    core.result.Result Unit NCX_Reference.PoolV1VerifierRegistryFormatError :=
 match r with | .Ok u => .Ok u | .Err e => .Err (NCX_Carrier.from_error e)

def registry (r : VerifierRegistryV2) : Result (core.result.Result Unit PoolV1VerifierRegistryFormatError) := do
 let reply ← NCX_Reference.validate_verifier_registry_v2 (NCX_Carrier.from_registry r)
 ok (port reply)

def entry (r : VerifierRegistryEntryV2) : Result (core.result.Result Unit PoolV1VerifierRegistryFormatError) := do
 let reply ← NCX_Reference.validate_verifier_registry_entry_v2 (NCX_Carrier.from_entry r)
 ok (port reply)

/-- Complete record port, not a fixture or a validation-success premise. -/
theorem registry_source (r : NCX_Reference.VerifierRegistryV2) :
    registry (NCX_Carrier.registry r) =
      (do let reply ← NCX_Reference.validate_verifier_registry_v2 r
          ok (port reply)) := by
  unfold registry
  rw [NCX_Carrier.registry_roundtrip]

theorem entry_source (r : NCX_Reference.VerifierRegistryEntryV2) :
    entry (NCX_Carrier.entry r) =
      (do let reply ← NCX_Reference.validate_verifier_registry_entry_v2 r
          ok (port reply)) := by
  unfold entry
  rw [NCX_Carrier.entry_roundtrip]

/-- Every error constructor and successful unit is retained by the carrier. -/
theorem result_roundtrip (r : core.result.Result Unit NCX_Reference.PoolV1VerifierRegistryFormatError) :
    unport (port r) = r := by
  cases r with
  | Ok u => rfl
  | Err e => exact congrArg core.result.Result.Err (NCX_Carrier.error_roundtrip e)

theorem inverse_result_roundtrip (r : core.result.Result Unit PoolV1VerifierRegistryFormatError) :
    port (unport r) = r := by
  cases r with
  | Ok u => rfl
  | Err e => exact congrArg core.result.Result.Err (NCX_Carrier.error_surjective e)

/-- Same typed32-byte child at every required-binding test in the extracted
validators. Native private helper K046/047 has this complete input domain. -/
theorem zero_child (value : Array U8 32#usize) :
    NCX_Reference.required_binding_is_zero value = NHY_ZeroBinding.binding_ref value := NHY_AllZeroBridge.source value

theorem native_registry_domain (r : VerifierRegistryV2) :
    NCX_Carrier.registry (NCX_Carrier.from_registry r)=r := NCX_Carrier.registry_surjective r

theorem native_entry_domain (r : VerifierRegistryEntryV2) :
    NCX_Carrier.entry (NCX_Carrier.from_entry r)=r := NCX_Carrier.entry_surjective r

#print axioms native_registry_domain
#print axioms native_entry_domain

#print axioms registry_source
#print axioms entry_source
#print axioms result_roundtrip
#print axioms inverse_result_roundtrip
#print axioms zero_child
end NHY_NCXValidators
