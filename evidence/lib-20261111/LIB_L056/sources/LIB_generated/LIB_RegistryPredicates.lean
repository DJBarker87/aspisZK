import NND_EntryV2Carrier
import NND_ScalarComparison
import NIS_ActiveSlots
import NHY_RegistrySlots
set_option autoImplicit false
namespace LIB_RegistryPredicates
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
open aspis_statement.pool_v1.verifier_registry

theorem paused1 (base : Ops) (r : VerifierRegistryV1) :
 (NHY_RegistrySlots.install base).op25 r = ok (registryV1 r).is_paused := by
 change NHY_RegistryReference.flag_ref r.flags 1#u8 = _
 simp only [NHY_RegistryReference.flag_ref,lift,bind_tc_ok]
 rw [flags]
 rfl

theorem immutable1 (base : Ops) (r : VerifierRegistryV1) :
 (NHY_RegistrySlots.install base).op26 r = ok (registryV1 r).is_immutable := by
 change NHY_RegistryReference.flag_ref r.flags 2#u8 = _
 simp only [NHY_RegistryReference.flag_ref,lift,bind_tc_ok]
 rw [flags]
 rfl

theorem paused2 (base : Ops) (r : VerifierRegistryV2) :
 (NHY_RegistrySlots.install base).op27 r = ok (registryV2 r).is_paused := by
 change NHY_RegistryReference.flag_ref r.flags 1#u8 = _
 simp only [NHY_RegistryReference.flag_ref,lift,bind_tc_ok]
 rw [flags]
 rfl

theorem immutable2 (base : Ops) (r : VerifierRegistryV2) :
 (NHY_RegistrySlots.install base).op28 r = ok (registryV2 r).is_immutable := by
 change NHY_RegistryReference.flag_ref r.flags 2#u8 = _
 simp only [NHY_RegistryReference.flag_ref,lift,bind_tc_ok]
 rw [flags]
 rfl

theorem active1 (r : VerifierRegistryEntryV1) (s : U64) :
 NIJ_ActiveSlots.op30 r s = ok ((entryV1 r).is_active_at (slot s)) := by
 cases h : r.status <;>
 simp [NIJ_ActiveSlots.op30,NIJ_ActiveSlots.active,NIJ_ActiveSlots.activeStatus,
   RSL.EntryV1.is_active_at,entryV1,status,h]
 rw [show RSL.NO_RETIREMENT_SLOT = slot 18446744073709551615#u64 from rfl,slot_beq]
 rfl

theorem active2 (r : VerifierRegistryEntryV2) (s : U64) :
 NIJ_ActiveSlots.op29 r s = ok ((entryV2 r).is_active_at (slot s)) := by
 cases h : r.status <;>
 simp [NIJ_ActiveSlots.op29,NIJ_ActiveSlots.active,NIJ_ActiveSlots.activeStatus,
   RSL.EntryV2.is_active_at,entryV2,status,h]
 rw [show RSL.NO_RETIREMENT_SLOT = slot 18446744073709551615#u64 from rfl,slot_beq]
 rfl

#print axioms paused1
#print axioms immutable1
#print axioms paused2
#print axioms immutable2
#print axioms active1
#print axioms active2
end LIB_RegistryPredicates
