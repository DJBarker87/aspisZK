import R1Z.PV_Src_PublicRootClosed
import R1Z.PV_Src_RecordAssociation
import R1Z.PV_Src_ExternalAssociation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_PublicInstalledRoot
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
variable {K : Type} [Field K] [CharP K 2147483647]

theorem correspondence (external : ExternalLinear) (records : Records)
    (external_law : PV_Src_ExternalAssociation.Associated external)
    (records_law : PV_Src_RecordAssociation.Associated external records)
    (i : Input) (success : @run external records i = ok (.Ok i.compiled))
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (r : pair_forest_copy_builder.CopyRecords) (hr : @newRecords records i = ok r) :
    PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic r.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput i))) := by
  have he := PV_Src_ExternalAssociation.dictionary external external_law
  have hrule := PV_Src_RecordAssociation.dictionary external records records_law
  rw [he] at hrule
  rw [he,hrule] at success
  rw [hrule] at hr
  exact PV_Src_PublicRootClosed.correspondence i success frontier r hr

#print axioms correspondence
end R1Z.PV_Src_PublicInstalledRoot
