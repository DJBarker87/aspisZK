import R1Z.PV_Src_PublicDeploymentAssociation
import R1Z.PV_Src_RecordRootReturned
set_option autoImplicit false
namespace R1Z.PV_Src_PublicRootAssociation
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput

theorem source {I : Type} (inputs : I → Input)
    (compile_call : ∀ i, @run PV_Src_ExternalReference.dictionary
      (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) (inputs i) =
        ok (.Ok (inputs i).compiled))
    (frontier : ∀ i (l : Fin 20), Canon8 (inputs i).snapshot.frontier.val[l.val]!) :
    PV_Src_PublicDeploymentAssociation.Association
      (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary) inputs where
  snapshot := fun i => @PV_Src_ReturnedSnapshot.returned_snapshot
    PV_Src_ExternalReference.dictionary (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary)
    (inputs i).witness (outputValue (inputs i).request) (recipient (inputs i).request)
    (inputs i).change (forestPublic (inputs i).request) (inputs i).laneAnchor
    (inputs i).snapshot (inputs i).compiled (compile_call i)
  frontier := frontier
  returned_public := by
    intro i r hr
    have he := Result.ok.inj (hr.symm.trans (PV_Src_RecordRootReturned.source (inputs i)))
    rw [he]
    rfl

#print axioms source
end R1Z.PV_Src_PublicRootAssociation
