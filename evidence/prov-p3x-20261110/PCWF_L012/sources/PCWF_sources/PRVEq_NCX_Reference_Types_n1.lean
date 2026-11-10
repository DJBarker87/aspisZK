-- PCWF item C (NCX_Reference.Types): fresh 4bb3b3f emission PCWF_E002 (aspis-statement, overflow-checks ON, root validate_verifier_registry_entry_v2)
-- types VerifierEntryStatusV1 (frozen: #[repr(u8)], fresh @[discriminant u8]) and VerifierRegistryEntryV2, against the gate NCX_Reference.Types
-- (reference crate without repr(u8): @[discriminant isize]). The two enums are distinct Lean inductives; this file proves the isomorphism.
import Aeneas
import NCX_Reference.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace NCX_Reference
namespace PRVFresh_NCX_Reference

/-- [aspis_statement::pool_v1::verifier_registry::VerifierEntryStatusV1]
    Source: 'crates/aspis-statement/src/pool_v1/verifier_registry.rs', lines 52:0-57:1
    Visibility: public -/
@[discriminant u8]
inductive pool_v1.verifier_registry.VerifierEntryStatusV1 where
| Pending : pool_v1.verifier_registry.VerifierEntryStatusV1
| Active : pool_v1.verifier_registry.VerifierEntryStatusV1
| Paused : pool_v1.verifier_registry.VerifierEntryStatusV1
| Retired : pool_v1.verifier_registry.VerifierEntryStatusV1

/-- [aspis_statement::pool_v1::verifier_registry::VerifierRegistryEntryV2]
    Source: 'crates/aspis-statement/src/pool_v1/verifier_registry.rs', lines 165:0-184:1
    Visibility: public -/
structure pool_v1.verifier_registry.VerifierRegistryEntryV2 where
  status : pool_v1.verifier_registry.VerifierEntryStatusV1
  statement_version : Std.U8
  bump : Std.U8
  pool : Array Std.U8 32#usize
  verifier_program : Array Std.U8 32#usize
  profile_binding : Array Std.U8 32#usize
  release_binding : Array Std.U8 32#usize
  loader_program : Array Std.U8 32#usize
  programdata_address : Array Std.U8 32#usize
  programdata_bump : Std.U8
  executable_hash : Array Std.U8 32#usize
  expected_upgrade_authority : Array Std.U8 32#usize
  activation_slot : Std.U64
  retirement_slot : Std.U64
  policy_binding : Array Std.U8 32#usize

end PRVFresh_NCX_Reference
end NCX_Reference

open NCX_Reference in
def PRVEq.NCX_Reference.Types.statusToFresh : VerifierEntryStatusV1 → PRVFresh_NCX_Reference.pool_v1.verifier_registry.VerifierEntryStatusV1
  | .Pending => .Pending | .Active => .Active | .Paused => .Paused | .Retired => .Retired

open NCX_Reference in
def PRVEq.NCX_Reference.Types.statusToGate : PRVFresh_NCX_Reference.pool_v1.verifier_registry.VerifierEntryStatusV1 → VerifierEntryStatusV1
  | .Pending => .Pending | .Active => .Active | .Paused => .Paused | .Retired => .Retired

open NCX_Reference in
theorem PRVEq.NCX_Reference.Types.status_left (x : VerifierEntryStatusV1) :
    PRVEq.NCX_Reference.Types.statusToGate (PRVEq.NCX_Reference.Types.statusToFresh x) = x := by
  cases x <;> rfl
#print axioms PRVEq.NCX_Reference.Types.status_left

open NCX_Reference in
theorem PRVEq.NCX_Reference.Types.status_right (x : PRVFresh_NCX_Reference.pool_v1.verifier_registry.VerifierEntryStatusV1) :
    PRVEq.NCX_Reference.Types.statusToFresh (PRVEq.NCX_Reference.Types.statusToGate x) = x := by
  cases x <;> rfl
#print axioms PRVEq.NCX_Reference.Types.status_right

-- The discriminant values agree: gate isize discriminant = fresh u8 discriminant, as integers, constructor by constructor.
open NCX_Reference in
theorem PRVEq.NCX_Reference.Types.status_discriminant (x : VerifierEntryStatusV1) :
    (VerifierEntryStatusV1.read_discriminant x).val =
      ((PRVFresh_NCX_Reference.pool_v1.verifier_registry.VerifierEntryStatusV1.read_discriminant
        (PRVEq.NCX_Reference.Types.statusToFresh x)).val : Int) := by
  cases x <;> simp [NCX_Reference.VerifierEntryStatusV1.read_discriminant, NCX_Reference.PRVFresh_NCX_Reference.pool_v1.verifier_registry.VerifierEntryStatusV1.read_discriminant, PRVEq.NCX_Reference.Types.statusToFresh]
#print axioms PRVEq.NCX_Reference.Types.status_discriminant

open NCX_Reference in
def PRVEq.NCX_Reference.Types.entryToFresh (e : VerifierRegistryEntryV2) : PRVFresh_NCX_Reference.pool_v1.verifier_registry.VerifierRegistryEntryV2 :=
  { status := PRVEq.NCX_Reference.Types.statusToFresh e.status, statement_version := e.statement_version, bump := e.bump, pool := e.pool,
    verifier_program := e.verifier_program, profile_binding := e.profile_binding, release_binding := e.release_binding,
    loader_program := e.loader_program, programdata_address := e.programdata_address, programdata_bump := e.programdata_bump,
    executable_hash := e.executable_hash, expected_upgrade_authority := e.expected_upgrade_authority,
    activation_slot := e.activation_slot, retirement_slot := e.retirement_slot, policy_binding := e.policy_binding }

open NCX_Reference in
def PRVEq.NCX_Reference.Types.entryToGate (e : PRVFresh_NCX_Reference.pool_v1.verifier_registry.VerifierRegistryEntryV2) : VerifierRegistryEntryV2 :=
  { status := PRVEq.NCX_Reference.Types.statusToGate e.status, statement_version := e.statement_version, bump := e.bump, pool := e.pool,
    verifier_program := e.verifier_program, profile_binding := e.profile_binding, release_binding := e.release_binding,
    loader_program := e.loader_program, programdata_address := e.programdata_address, programdata_bump := e.programdata_bump,
    executable_hash := e.executable_hash, expected_upgrade_authority := e.expected_upgrade_authority,
    activation_slot := e.activation_slot, retirement_slot := e.retirement_slot, policy_binding := e.policy_binding }

open NCX_Reference in
theorem PRVEq.NCX_Reference.Types.entry_left (e : VerifierRegistryEntryV2) :
    PRVEq.NCX_Reference.Types.entryToGate (PRVEq.NCX_Reference.Types.entryToFresh e) = e := by
  obtain ⟨s, _⟩ := e
  simp only [PRVEq.NCX_Reference.Types.entryToGate, PRVEq.NCX_Reference.Types.entryToFresh, PRVEq.NCX_Reference.Types.status_left]
#print axioms PRVEq.NCX_Reference.Types.entry_left

open NCX_Reference in
theorem PRVEq.NCX_Reference.Types.entry_right (e : PRVFresh_NCX_Reference.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
    PRVEq.NCX_Reference.Types.entryToFresh (PRVEq.NCX_Reference.Types.entryToGate e) = e := by
  obtain ⟨s, _⟩ := e
  simp only [PRVEq.NCX_Reference.Types.entryToGate, PRVEq.NCX_Reference.Types.entryToFresh, PRVEq.NCX_Reference.Types.status_right]
#print axioms PRVEq.NCX_Reference.Types.entry_right
