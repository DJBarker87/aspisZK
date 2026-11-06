import NJI_V1Carrier
set_option autoImplicit false
noncomputable section
namespace NJI_V1Models
open Aeneas Aeneas.Std Result
open NJI_V1Carrier
attribute [local instance] Classical.propDecidable
abbrev Z (v : Array U8 32#usize) := decide (v=Array.repeat 32#usize 0#u8)

def registry (r : R) : Result (core.result.Result Unit F) :=
 if r.flags &&& (~~~ 3#u8) != 0#u8 then ok (.Err .UnsupportedFlags)
 else if Z r.pool then ok (.Err .ZeroRequiredBinding)
 else if Z r.policy_binding then ok (.Err .ZeroRequiredBinding)
 else if (r.flags &&& 2#u8 != 0#u8) != Z r.authority then ok (.Err .InvalidAuthorityMode)
 else if r.minimum_activation_delay_slots=0#u64 then ok (.Err .InvalidActivationDelay)
 else ok (.Ok ())

def entry (r : E) : Result (core.result.Result Unit F) :=
 if r.statement_version=0#u8 then ok (.Err .InvalidStatementVersion)
 else if Z r.pool then ok (.Err .ZeroRequiredBinding)
 else if Z r.verifier_program then ok (.Err .ZeroRequiredBinding)
 else if Z r.profile_binding then ok (.Err .ZeroRequiredBinding)
 else if Z r.release_binding then ok (.Err .ZeroRequiredBinding)
 else if Z r.policy_binding then ok (.Err .ZeroRequiredBinding)
 else if r.retirement_slot=18446744073709551615#u64 then ok (.Ok ())
 else if r.retirement_slot≤r.activation_slot then ok (.Err .InvalidRetirementSlot)
 else ok (.Ok ())

/-- Existing CLOSED zero-binding child; exact new emitted body is the same library call. -/
theorem zero_source (v : Array U8 32#usize) :
 NJI_Extracted.aspis_statement.pool_v1.verifier_registry.required_binding_is_zero v = ok (Z v) :=
 NHY_ZeroBinding.source v

/-- Every original error and Ok, no success premise or callback law. -/
theorem registry_source (r : R) :
 NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_v1 r = registry r := by
 have mask : NJI_Extracted.aspis_statement.pool_v1.verifier_registry.POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK = ok 3#u8 := by
  unfold NJI_Extracted.aspis_statement.pool_v1.verifier_registry.POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK NJI_Extracted.aspis_statement.pool_v1.verifier_registry.POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED NJI_Extracted.aspis_statement.pool_v1.verifier_registry.POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE
  rfl
 have immutable : NJI_Extracted.aspis_statement.pool_v1.verifier_registry.POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE = ok 2#u8 := by
  unfold NJI_Extracted.aspis_statement.pool_v1.verifier_registry.POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE
  rfl
 simp only [NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_v1,
  mask,
  NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1.is_immutable,
  immutable,
  lift,bind_tc_ok,zero_source,registry]

/-- Retirement sentinel and all early rejects retain the emitted full Result. -/
theorem entry_source (r : E) :
 NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_entry_v1 r = entry r := by
 have sentinel : NJI_Extracted.aspis_statement.pool_v1.verifier_registry.POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT = 18446744073709551615#u64 := by
  unfold NJI_Extracted.aspis_statement.pool_v1.verifier_registry.POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT core.num.U64.MAX
  rfl
 simp only [NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_entry_v1,
  NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1.has_no_retirement_slot,
  sentinel,
  lift,bind_tc_ok,zero_source,entry,decide_eq_true_eq]

#print axioms zero_source
#print axioms registry_source
#print axioms entry_source
end NJI_V1Models
