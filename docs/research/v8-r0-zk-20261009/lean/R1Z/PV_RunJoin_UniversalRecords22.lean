import R1Z.PV_RunJoin_CompilerDictionary16
import R1Z.PV_Src_PublicDeploymentAssociation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_UniversalRecords22
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_CompilerDictionary16.shipped

/-- The general shipped Records identification fixes the actual returned
record, for every argument tuple, without a fixture or execution premise. -/
theorem returned (i : Input) (r : pair_forest_copy_builder.CopyRecords)
    (hr : @newRecords R i = ok r) :
    r = PV_Src_RecordReference.returned PV_Src_CanonicalRoots.table i := by
  rw [PV_RunJoin_CompilerDictionary16.newRecords] at hr
  exact (Result.ok.inj hr).symm
#print axioms returned

theorem public_record (i : Input) (r : pair_forest_copy_builder.CopyRecords)
    (hr : @newRecords R i = ok r) :
    PV_Src_Forest_PrimitiveArguments.wordPublic r.p =
      PV_Src_PublicHeader.publicRecord PV_Src_CanonicalRoots.table i := by
  rw [returned i r hr]
  rfl
#print axioms public_record

theorem snapshot (i : Input)
    (success : @run E R i = ok (.Ok i.compiled)) :
    i.compiled.public_statement.live_snapshot = i.snapshot :=
  @PV_Src_ReturnedSnapshot.returned_snapshot E R i.witness (outputValue i.request)
    (recipient i.request) i.change (forestPublic i.request) i.laneAnchor i.snapshot
    i.compiled success
#print axioms snapshot

theorem words (i : Input) (checked : PV_Src_RecordReference.Checked i)
    (r : pair_forest_copy_builder.CopyRecords) (hr : @newRecords R i = ok r) :
    WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness r.w) := by
  apply PV_Src_RecordReference.words PV_Src_CanonicalRoots.table i checked r
  rw [← PV_RunJoin_CompilerDictionary16.frozen_dictionary]
  exact hr
#print axioms words

/-- No installed-record association is required: only canonical frontier
words and a successful return remain in this universal publicCorr lemma. -/
theorem publicCorr {K : Type} [Field K] [CharP K 2147483647]
    (i : Input) (success : @run E R i = ok (.Ok i.compiled))
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!)
    (r : pair_forest_copy_builder.CopyRecords) (hr : @newRecords R i = ok r) :
    PubCorr (PV_Src_Forest_PrimitiveArguments.wordPublic r.p)
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput i))) := by
  rw [public_record i r hr]
  exact PV_Src_PublicParts.reference_parts PV_Src_CanonicalRoots.table i
    (snapshot i success) frontier PV_Src_CanonicalRoots.meaning
    (fun l => PV_Src_CanonicalRoots.canonical l.castSucc)
#print axioms publicCorr
end R1Z.PV_RunJoin_UniversalRecords22
