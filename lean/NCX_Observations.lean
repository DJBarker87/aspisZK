import NCX_Carrier
import NCV_ArrayFrame
set_option autoImplicit false
namespace NCX_Observations
open Aeneas Aeneas.Std Result
inductive Observation where
 | byte : U8 → Observation
 | word : U64 → Observation
 | status : NCX_Reference.VerifierEntryStatusV1 → Observation

def registry (v : NCX_Reference.VerifierRegistryV2) (field j : Nat) : Observation :=
  match field with
  | 0 => .byte v.flags
  | 1 => .byte v.bump
  | 2 => .byte (NCV_ArrayFrame.coord v.pool j)
  | 3 => .byte (NCV_ArrayFrame.coord v.authority j)
  | 4 => .byte (NCV_ArrayFrame.coord v.policy_binding j)
  | 5 => .word v.generation
  | 6 => .word v.minimum_activation_delay_slots
  | 7 => .byte (NCV_ArrayFrame.coord v.registry_program j)
  | 8 => .byte (NCV_ArrayFrame.coord v.loader_program j)
  | 9 => .byte (NCV_ArrayFrame.coord v.programdata_address j)
  | 10 => .byte v.programdata_bump
  | 11 => .byte (NCV_ArrayFrame.coord v.executable_hash j)
  | _ => .byte 0#u8

/-- Full record equality follows from arbitrary field and byte observations. -/
theorem registry_injective (a b : NCX_Reference.VerifierRegistryV2)
    (same : ∀ field j, field<12 → j<32 → registry a field j=registry b field j) : a=b := by
  have e_flags : a.flags=b.flags := by
    exact Observation.byte.inj (same 0 0 (by omega) (by omega))
  have e_bump : a.bump=b.bump := by
    exact Observation.byte.inj (same 1 0 (by omega) (by omega))
  have e_pool : a.pool=b.pool := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 2 j (by omega) hj
    exact Observation.byte.inj h
  have e_authority : a.authority=b.authority := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 3 j (by omega) hj
    exact Observation.byte.inj h
  have e_policy_binding : a.policy_binding=b.policy_binding := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 4 j (by omega) hj
    exact Observation.byte.inj h
  have e_generation : a.generation=b.generation := by
    exact Observation.word.inj (same 5 0 (by omega) (by omega))
  have e_minimum_activation_delay_slots : a.minimum_activation_delay_slots=b.minimum_activation_delay_slots := by
    exact Observation.word.inj (same 6 0 (by omega) (by omega))
  have e_registry_program : a.registry_program=b.registry_program := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 7 j (by omega) hj
    exact Observation.byte.inj h
  have e_loader_program : a.loader_program=b.loader_program := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 8 j (by omega) hj
    exact Observation.byte.inj h
  have e_programdata_address : a.programdata_address=b.programdata_address := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 9 j (by omega) hj
    exact Observation.byte.inj h
  have e_programdata_bump : a.programdata_bump=b.programdata_bump := by
    exact Observation.byte.inj (same 10 0 (by omega) (by omega))
  have e_executable_hash : a.executable_hash=b.executable_hash := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 11 j (by omega) hj
    exact Observation.byte.inj h
  cases a;cases b
  cases e_flags;cases e_bump;cases e_pool;cases e_authority;cases e_policy_binding;cases e_generation;cases e_minimum_activation_delay_slots;cases e_registry_program;cases e_loader_program;cases e_programdata_address;cases e_programdata_bump;cases e_executable_hash
  rfl
#print axioms registry_injective

def entry (v : NCX_Reference.VerifierRegistryEntryV2) (field j : Nat) : Observation :=
  match field with
  | 0 => .status v.status
  | 1 => .byte v.statement_version
  | 2 => .byte v.bump
  | 3 => .byte (NCV_ArrayFrame.coord v.pool j)
  | 4 => .byte (NCV_ArrayFrame.coord v.verifier_program j)
  | 5 => .byte (NCV_ArrayFrame.coord v.profile_binding j)
  | 6 => .byte (NCV_ArrayFrame.coord v.release_binding j)
  | 7 => .byte (NCV_ArrayFrame.coord v.loader_program j)
  | 8 => .byte (NCV_ArrayFrame.coord v.programdata_address j)
  | 9 => .byte v.programdata_bump
  | 10 => .byte (NCV_ArrayFrame.coord v.executable_hash j)
  | 11 => .byte (NCV_ArrayFrame.coord v.expected_upgrade_authority j)
  | 12 => .word v.activation_slot
  | 13 => .word v.retirement_slot
  | 14 => .byte (NCV_ArrayFrame.coord v.policy_binding j)
  | _ => .byte 0#u8

/-- Full record equality follows from arbitrary field and byte observations. -/
theorem entry_injective (a b : NCX_Reference.VerifierRegistryEntryV2)
    (same : ∀ field j, field<15 → j<32 → entry a field j=entry b field j) : a=b := by
  have e_status : a.status=b.status := by
    exact Observation.status.inj (same 0 0 (by omega) (by omega))
  have e_statement_version : a.statement_version=b.statement_version := by
    exact Observation.byte.inj (same 1 0 (by omega) (by omega))
  have e_bump : a.bump=b.bump := by
    exact Observation.byte.inj (same 2 0 (by omega) (by omega))
  have e_pool : a.pool=b.pool := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 3 j (by omega) hj
    exact Observation.byte.inj h
  have e_verifier_program : a.verifier_program=b.verifier_program := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 4 j (by omega) hj
    exact Observation.byte.inj h
  have e_profile_binding : a.profile_binding=b.profile_binding := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 5 j (by omega) hj
    exact Observation.byte.inj h
  have e_release_binding : a.release_binding=b.release_binding := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 6 j (by omega) hj
    exact Observation.byte.inj h
  have e_loader_program : a.loader_program=b.loader_program := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 7 j (by omega) hj
    exact Observation.byte.inj h
  have e_programdata_address : a.programdata_address=b.programdata_address := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 8 j (by omega) hj
    exact Observation.byte.inj h
  have e_programdata_bump : a.programdata_bump=b.programdata_bump := by
    exact Observation.byte.inj (same 9 0 (by omega) (by omega))
  have e_executable_hash : a.executable_hash=b.executable_hash := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 10 j (by omega) hj
    exact Observation.byte.inj h
  have e_expected_upgrade_authority : a.expected_upgrade_authority=b.expected_upgrade_authority := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 11 j (by omega) hj
    exact Observation.byte.inj h
  have e_activation_slot : a.activation_slot=b.activation_slot := by
    exact Observation.word.inj (same 12 0 (by omega) (by omega))
  have e_retirement_slot : a.retirement_slot=b.retirement_slot := by
    exact Observation.word.inj (same 13 0 (by omega) (by omega))
  have e_policy_binding : a.policy_binding=b.policy_binding := by
    apply NCV_ArrayFrame.whole
    intro j hj _
    have h:=same 14 j (by omega) hj
    exact Observation.byte.inj h
  cases a;cases b
  cases e_status;cases e_statement_version;cases e_bump;cases e_pool;cases e_verifier_program;cases e_profile_binding;cases e_release_binding;cases e_loader_program;cases e_programdata_address;cases e_programdata_bump;cases e_executable_hash;cases e_expected_upgrade_authority;cases e_activation_slot;cases e_retirement_slot;cases e_policy_binding
  rfl
#print axioms entry_injective
end NCX_Observations
