import R1Z.PV_Src_RootHelper
import R1Z.PV_Src_DynamicPublic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_PublicRootClosed
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
variable {K : Type} [Field K] [CharP K 2147483647]

theorem correspondence (i : Input)
    (success : @run PV_Src_ExternalReference.dictionary
      (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) i = ok (.Ok i.compiled))
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (r : pair_forest_copy_builder.CopyRecords)
    (hr : @newRecords (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) i = ok r) :
    PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic r.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput i))) :=
  @PV_Src_DynamicPublic.correspondence K _ _ PV_Src_ExternalReference.dictionary
    i success frontier PV_Src_RootHelper.source r hr

#print axioms correspondence
end R1Z.PV_Src_PublicRootClosed
