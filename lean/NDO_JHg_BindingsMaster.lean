import JHg_AuditMaster
import NDO_JHg_AuditDomains
import NDO_JHg_World
import NDO_JFs_Cell00
import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.JHg_BindingsMaster
open Aeneas Aeneas.Std Result

theorem pool : (JHg_DataMaster.bytes.drop 72).take 32=JFu_PublicBindings.pool.val := by
  rw [JHg_AuditMaster.pool];rfl
#print axioms pool
theorem master_key : (JHg_DataMaster.bytes.drop 72).take 32=(JHg_World.e2.snapshot 1 384 384).key.val := by
  rw [JHg_AuditMaster.pool];rfl
#print axioms master_key
theorem registry_program : (JHg_DataMaster.bytes.drop 216).take 32=JHb_Programs.registry.val := by
  rw [JHg_AuditMaster.registry_program];rfl
#print axioms registry_program
theorem policy : (JHg_DataMaster.bytes.drop 280).take 32=AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING.val := by
  rw [JHg_AuditMaster.policy_binding]
  unfold AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING
  rfl
#print axioms policy
end AspisR1.JHg_BindingsMaster
