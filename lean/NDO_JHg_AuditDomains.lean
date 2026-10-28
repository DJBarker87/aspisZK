import JHg_AuditMaster
import JHg_AuditForest
import NDO_JHf_OffsetModel
set_option autoImplicit false
namespace AspisR1.JHg_AuditDomains
open Aeneas Aeneas.Std Result

theorem master : (JHg_DataMaster.bytes.drop 176).take 32=JFt_SnapshotValue.value.deployment_domain.val := by
  rw [JHg_AuditMaster.domain,JHf_OffsetModel.retained_public]
#print axioms master
theorem checkpoint : (JHg_DataForest.bytes.drop 40).take 32=JFt_SnapshotValue.value.deployment_domain.val := by
  rw [JHg_AuditForest.domain,JHf_OffsetModel.retained_public]
#print axioms checkpoint

theorem target : (JHg_DataMaster.bytes.drop 176).take 32=JFu_PublicBindings.domain.val := master
#print axioms target

theorem agreement : (JHg_DataMaster.bytes.drop 176).take 32=(JHg_DataForest.bytes.drop 40).take 32 :=
  master.trans checkpoint.symm
#print axioms agreement
end AspisR1.JHg_AuditDomains
