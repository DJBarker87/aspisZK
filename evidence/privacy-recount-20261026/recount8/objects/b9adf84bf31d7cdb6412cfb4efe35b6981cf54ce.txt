import R1Z.PV_RunJoin_PackedPublic
import R1Z.PV_Src_CanonicalPrivateRecord
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PackedRecords
open Aeneas Aeneas.Std Result R1J.SpendWitnessMap
open BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def input (i : PV_Src_CheckedCanonical.Data (K := K)) :=
  PV_Src_CheckedCanonical.input (PV_Src_PackedSelection.select i)

theorem private_record (i : PV_Src_CheckedCanonical.Data (K := K)) :
    input i = PV_Src_CanonicalPrivateRecord.input i.canonical i.pool i.domain
      i.destination i.snapshot i.compiled i.laneAnchor := rfl

theorem checked (i : PV_Src_CheckedCanonical.Data (K := K)) :
    PV_Src_RecordReference.Checked (input i) := PV_Src_PackedSelection.checked i

theorem admission (i : PV_Src_CheckedCanonical.Data (K := K))
    (roots : BuilderRecordsReference.Roots)
    (publicEq : mapPub (K := K) (PV_Src_Public.canonicalPublic
      (PV_Src_NativeInput.publicInput (input i))) = mapPub (K := K) i.canonical.val.1) :
    BuilderSpendRelation.RspendPlus
      (mapPub (K := K) (PV_Src_Public.canonicalPublic (PV_Src_NativeInput.publicInput (input i))))
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness
        (PV_Src_Forest_PrimitiveArguments.wordWitness
          (PV_Src_RecordReference.returned roots (input i)).w))) :=
  PV_Src_CanonicalPrivateRecord.admission i.canonical roots i.pool i.domain i.destination
    i.snapshot i.compiled i.laneAnchor _
    (PV_Src_RecordReference.newRecords_eq roots _) publicEq

/-- Exact success remains an execution fact about the supplied dictionaries;
checked/path packing does not imply it. Successful output is unique. -/
theorem returned_unique [BuilderForestAdmissionPort.ExternalLinear] [BuilderForestAdmissionPort.Records]
    (i : PV_Src_CheckedCanonical.Data (K := K))
    (actual : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (success : PV_Src_NativeInput.run (input i) = ok (.Ok actual))
    (selected : PV_Src_NativeInput.run (input i) = ok (.Ok (input i).compiled)) :
    actual = (input i).compiled := by
  rw [success] at selected
  exact core.result.Result.Ok.inj (Result.ok.inj selected)

#print axioms private_record
#print axioms checked
#print axioms admission
#print axioms returned_unique
end R1Z.PV_RunJoin_PackedRecords
