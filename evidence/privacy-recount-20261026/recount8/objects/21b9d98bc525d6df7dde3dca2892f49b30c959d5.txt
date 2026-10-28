import R1Z.PV_RunJoin_PackedRecords
import R1Z.PV_Src_DynamicAdmission
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PackedDynamic
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Dynamic source dictionary admission at the same path-packed record.
The dictionary's shipped mapper equality and public association remain P. -/
theorem admission [ExternalLinear] (i : PV_Src_CheckedCanonical.Data (K := K))
    (records : pair_forest_copy_builder.CopyRecords)
    (hr : @PV_Src_NativeInput.newRecords PV_Src_RecordDynamic.dictionary
      (PV_RunJoin_PackedRecords.input i) = ok records)
    (publicEq : mapPub (K := K) (PV_Src_Public.canonicalPublic
      (PV_Src_NativeInput.publicInput (PV_RunJoin_PackedRecords.input i))) =
      mapPub (K := K) i.canonical.val.1) :
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic
        (PV_Src_NativeInput.publicInput (PV_RunJoin_PackedRecords.input i))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness
        (PV_Src_Forest_PrimitiveArguments.wordWitness records.w))) :=
  PV_Src_DynamicAdmission.selected i.canonical i.pool i.domain i.destination
    i.snapshot i.compiled i.laneAnchor records hr publicEq

/-- The native dictionary equality is explicit; it is never installed as T. -/
theorem installed_admission [ExternalLinear]
    (actualRecords : Records) (source : actualRecords = PV_Src_RecordDynamic.dictionary)
    (i : PV_Src_CheckedCanonical.Data (K := K))
    (records : pair_forest_copy_builder.CopyRecords)
    (hr : @PV_Src_NativeInput.newRecords actualRecords (PV_RunJoin_PackedRecords.input i) = ok records)
    (publicEq : mapPub (K := K) (PV_Src_Public.canonicalPublic
      (PV_Src_NativeInput.publicInput (PV_RunJoin_PackedRecords.input i))) =
      mapPub (K := K) i.canonical.val.1) :
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic
        (PV_Src_NativeInput.publicInput (PV_RunJoin_PackedRecords.input i))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness
        (PV_Src_Forest_PrimitiveArguments.wordWitness records.w))) := by
  rw [source] at hr
  exact admission i records hr publicEq

#print axioms admission
#print axioms installed_admission
end R1Z.PV_RunJoin_PackedDynamic
