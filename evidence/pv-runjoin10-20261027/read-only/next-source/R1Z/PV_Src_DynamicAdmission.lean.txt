import R1Z.PV_Src_CanonicalPrivateRecord
import R1Z.PV_Src_RecordDynamic

/-! Admission for the same normalized canonical input through the dynamic pure
record dictionary. The public/snapshot association remains an explicit source
join. No equality to the shipped mapper or compiler success is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_DynamicAdmission
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem selected [ExternalLinear] (c : BuilderCanonical.Instance (K := K))
    (pool domain destination : PV_Src_PublicRecords.Context)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize)
    (records : pair_forest_copy_builder.CopyRecords)
    (hr : @PV_Src_NativeInput.newRecords PV_Src_RecordDynamic.dictionary
      (PV_Src_CanonicalPrivateRecord.input c pool domain destination snapshot compiled anchor) = ok records)
    (publicEq : mapPub (K := K) (PV_Src_Public.canonicalPublic
      (PV_Src_NativeInput.publicInput
        (PV_Src_CanonicalPrivateRecord.input c pool domain destination snapshot compiled anchor))) =
      mapPub (K := K) c.val.1) :
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic
        (PV_Src_NativeInput.publicInput
          (PV_Src_CanonicalPrivateRecord.input c pool domain destination snapshot compiled anchor))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness
        (PV_Src_Forest_PrimitiveArguments.wordWitness records.w))) := by
  obtain ⟨roots,_,hrecords⟩ := PV_Src_RecordDynamic.newRecords_factor _ records hr
  exact PV_Src_CanonicalPrivateRecord.admission c roots pool domain destination
    snapshot compiled anchor records hrecords publicEq

#print axioms selected
end R1Z.PV_Src_DynamicAdmission
