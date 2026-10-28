import NCX_Reference.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NCX_Carrier
open Aeneas Aeneas.Std Result
open AdapterRw.aspis_statement.pool_v1.verifier_registry

def status : NCX_Reference.VerifierEntryStatusV1 → VerifierEntryStatusV1
  | .Pending => .Pending
  | .Active => .Active
  | .Paused => .Paused
  | .Retired => .Retired

def from_status : VerifierEntryStatusV1 → NCX_Reference.VerifierEntryStatusV1
  | .Pending => .Pending
  | .Active => .Active
  | .Paused => .Paused
  | .Retired => .Retired

def error : NCX_Reference.PoolV1VerifierRegistryFormatError → PoolV1VerifierRegistryFormatError
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .NonZeroReserved => .NonZeroReserved
  | .UnsupportedFlags => .UnsupportedFlags
  | .InvalidStatus => .InvalidStatus
  | .InvalidAuthorityMode => .InvalidAuthorityMode
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidActivationDelay => .InvalidActivationDelay
  | .InvalidStatementVersion => .InvalidStatementVersion
  | .InvalidRetirementSlot => .InvalidRetirementSlot
  | .InvalidDeploymentMode => .InvalidDeploymentMode

def from_error : PoolV1VerifierRegistryFormatError → NCX_Reference.PoolV1VerifierRegistryFormatError
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .NonZeroReserved => .NonZeroReserved
  | .UnsupportedFlags => .UnsupportedFlags
  | .InvalidStatus => .InvalidStatus
  | .InvalidAuthorityMode => .InvalidAuthorityMode
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidActivationDelay => .InvalidActivationDelay
  | .InvalidStatementVersion => .InvalidStatementVersion
  | .InvalidRetirementSlot => .InvalidRetirementSlot
  | .InvalidDeploymentMode => .InvalidDeploymentMode

def registry (v : NCX_Reference.VerifierRegistryV2) : VerifierRegistryV2 :=
  ⟨v.flags,v.bump,v.pool,v.authority,v.policy_binding,v.generation,v.minimum_activation_delay_slots,v.registry_program,v.loader_program,v.programdata_address,v.programdata_bump,v.executable_hash⟩

def from_registry (v : VerifierRegistryV2) : NCX_Reference.VerifierRegistryV2 :=
  ⟨v.flags,v.bump,v.pool,v.authority,v.policy_binding,v.generation,v.minimum_activation_delay_slots,v.registry_program,v.loader_program,v.programdata_address,v.programdata_bump,v.executable_hash⟩

def entry (v : NCX_Reference.VerifierRegistryEntryV2) : VerifierRegistryEntryV2 :=
  ⟨status v.status,v.statement_version,v.bump,v.pool,v.verifier_program,v.profile_binding,v.release_binding,v.loader_program,v.programdata_address,v.programdata_bump,v.executable_hash,v.expected_upgrade_authority,v.activation_slot,v.retirement_slot,v.policy_binding⟩

def from_entry (v : VerifierRegistryEntryV2) : NCX_Reference.VerifierRegistryEntryV2 :=
  ⟨from_status v.status,v.statement_version,v.bump,v.pool,v.verifier_program,v.profile_binding,v.release_binding,v.loader_program,v.programdata_address,v.programdata_bump,v.executable_hash,v.expected_upgrade_authority,v.activation_slot,v.retirement_slot,v.policy_binding⟩

theorem status_roundtrip (v : NCX_Reference.VerifierEntryStatusV1) : from_status (status v)=v := by
  cases v <;> rfl
#print axioms status_roundtrip

theorem status_surjective (v : VerifierEntryStatusV1) : status (from_status v)=v := by
  cases v <;> rfl
#print axioms status_surjective

theorem error_roundtrip (v : NCX_Reference.PoolV1VerifierRegistryFormatError) : from_error (error v)=v := by
  cases v <;> rfl
#print axioms error_roundtrip

theorem error_surjective (v : PoolV1VerifierRegistryFormatError) : error (from_error v)=v := by
  cases v <;> rfl
#print axioms error_surjective

theorem registry_roundtrip (v : NCX_Reference.VerifierRegistryV2) : from_registry (registry v)=v := by
  cases v <;> rfl
#print axioms registry_roundtrip

theorem registry_surjective (v : VerifierRegistryV2) : registry (from_registry v)=v := by
  cases v <;> rfl
#print axioms registry_surjective

theorem entry_roundtrip (v : NCX_Reference.VerifierRegistryEntryV2) : from_entry (entry v)=v := by
  cases v with | mk st _ _ _ _ _ _ _ _ _ _ _ _ _ _ => cases st <;> rfl
#print axioms entry_roundtrip

theorem entry_surjective (v : VerifierRegistryEntryV2) : entry (from_entry v)=v := by
  cases v with | mk st _ _ _ _ _ _ _ _ _ _ _ _ _ _ => cases st <;> rfl
#print axioms entry_surjective
end NCX_Carrier
