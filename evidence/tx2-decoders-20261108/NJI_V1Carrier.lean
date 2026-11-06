import NJI_Extracted.Core

import NHY_NCXValidators

set_option autoImplicit false

noncomputable section

namespace NJI_V1Carrier

open Aeneas Aeneas.Std Result

abbrev R := NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1

abbrev E := NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1

abbrev S := NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1

abbrev F := NJI_Extracted.aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError

abbrev CR := AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1

abbrev CE := AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1

abbrev CS := AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1

abbrev CF := AdapterRw.aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError

def status : S → CS
 | .Pending => .Pending
 | .Active => .Active
 | .Paused => .Paused
 | .Retired => .Retired

def from_status : CS → S
 | .Pending => .Pending
 | .Active => .Active
 | .Paused => .Paused
 | .Retired => .Retired

def error : F → CF
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

def from_error : CF → F
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

def registry (v : R) : CR :=
 ⟨v.flags,v.bump,v.pool,v.authority,v.policy_binding,v.generation,v.minimum_activation_delay_slots⟩

def from_registry (v : CR) : R :=
 ⟨v.flags,v.bump,v.pool,v.authority,v.policy_binding,v.generation,v.minimum_activation_delay_slots⟩

def entry (v : E) : CE :=
 ⟨status v.status,v.statement_version,v.bump,v.pool,v.verifier_program,v.profile_binding,v.release_binding,v.activation_slot,v.retirement_slot,v.policy_binding⟩

def from_entry (v : CE) : E :=
 ⟨from_status v.status,v.statement_version,v.bump,v.pool,v.verifier_program,v.profile_binding,v.release_binding,v.activation_slot,v.retirement_slot,v.policy_binding⟩

theorem status_roundtrip (v : S) : from_status (status v)=v := by
 cases v <;> rfl

#print axioms status_roundtrip

theorem status_surjective (v : CS) : status (from_status v)=v := by
 cases v <;> rfl

#print axioms status_surjective

theorem error_roundtrip (v : F) : from_error (error v)=v := by
 cases v <;> rfl

#print axioms error_roundtrip

theorem error_surjective (v : CF) : error (from_error v)=v := by
 cases v <;> rfl

#print axioms error_surjective

theorem registry_roundtrip (v : R) : from_registry (registry v)=v := by
 cases v <;> simp only [registry,from_registry]

#print axioms registry_roundtrip

theorem registry_surjective (v : CR) : registry (from_registry v)=v := by
 cases v <;> simp only [registry,from_registry]

#print axioms registry_surjective

theorem entry_roundtrip (v : E) : from_entry (entry v)=v := by
 cases v <;> simp only [entry,from_entry,status_roundtrip]

#print axioms entry_roundtrip

theorem entry_surjective (v : CE) : entry (from_entry v)=v := by
 cases v <;> simp only [entry,from_entry,status_surjective]

#print axioms entry_surjective

def port (r : core.result.Result Unit F) : core.result.Result Unit CF :=
 match r with | .Ok u => .Ok u | .Err e => .Err (error e)

def unport (r : core.result.Result Unit CF) : core.result.Result Unit F :=
 match r with | .Ok u => .Ok u | .Err e => .Err (from_error e)

theorem result_roundtrip (r : core.result.Result Unit F) : unport (port r)=r := by
 cases r with
 | Ok u => rfl
 | Err e => exact congrArg core.result.Result.Err (error_roundtrip e)

#print axioms result_roundtrip

end NJI_V1Carrier
