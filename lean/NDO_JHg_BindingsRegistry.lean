import JHg_AuditRegistry
import JHg_AuditEntry
import NDO_JHg_World
import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.JHg_BindingsRegistry
open Aeneas Aeneas.Std Result

theorem pool : (JHb_DataRegistry.bytes.drop 8).take 32=(JHg_World.e2.snapshot 1 384 384).key.val := by
  rw [JHg_AuditRegistry.pool];rfl
#print axioms pool
theorem entry_pool : (JHb_DataEntry.bytes.drop 8).take 32=(JHg_World.e2.snapshot 1 384 384).key.val := by
  rw [JHg_AuditEntry.pool];rfl
#print axioms entry_pool
theorem verifier : (JHb_DataEntry.bytes.drop 40).take 32=CPH_Program.verifier.val := by
  rw [JHg_AuditEntry.verifier];rfl
#print axioms verifier
theorem profile : (JHb_DataEntry.bytes.drop 72).take 32=AdapterRw.r1_pool_adapter.PROFILE_BINDING.val := by
  rw [JHg_AuditEntry.profile]
  unfold AdapterRw.r1_pool_adapter.PROFILE_BINDING
  rfl
#print axioms profile
theorem release : (JHb_DataEntry.bytes.drop 104).take 32=AdapterRw.r1_pool_adapter.RELEASE_BINDING.val := by
  rw [JHg_AuditEntry.release]
  unfold AdapterRw.r1_pool_adapter.RELEASE_BINDING
  rfl
#print axioms release
theorem policy : (JHb_DataRegistry.bytes.drop 72).take 32=AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING.val := by
  rw [JHg_AuditRegistry.policy]
  unfold AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING
  rfl
#print axioms policy
theorem entry_policy : (JHb_DataEntry.bytes.drop 280).take 32=AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING.val := by
  rw [JHg_AuditEntry.policy]
  unfold AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING
  rfl
#print axioms entry_policy
theorem program : (JHb_DataRegistry.bytes.drop 120).take 32=JHb_Programs.registry.val := by
  rw [JHg_AuditRegistry.program];rfl
#print axioms program
end AspisR1.JHg_BindingsRegistry
