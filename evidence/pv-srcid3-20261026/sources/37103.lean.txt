import R1Z.PV_Src_RecordDynamic

/-! Complete Result equation for the extracted owned-reference dictionary.
This does not identify the still opaque shipped Records leaf. The equation
holds for arbitrary inputs and preserves every Result constructor of the
actual root helper; no success or total-effect hypothesis is introduced. -/
set_option autoImplicit false
namespace R1Z.PV_Src_DynamicCallEquation
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

def returned
    (roots : BuilderRecordsReference.Roots)
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :=
  (PV_Src_RecordReference.witness
    (BuilderRecordsReference.witness (PV_Src_NativeDirections.reference input)
      out (rec.map PV_Src_RecordReference.note) (PV_Src_RecordReference.note chg)),
   PV_Src_RecordReference.publicRecord
    (BuilderRecordsReference.publicRecord (rec.map PV_Src_RecordReference.note)
      (PV_Src_RecordReference.snapshot s) asset roots))

theorem reference_call
    (roots : BuilderRecordsReference.Roots)
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    PV_Src_RecordReference.call roots input out rec chg s asset =
      ok (returned roots input out rec chg s asset) := by
  unfold PV_Src_RecordReference.call
  rw [BuilderRecordsReference.records]
  rfl

theorem call [ExternalLinear]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    @Records.call PV_Src_RecordDynamic.dictionary input out rec chg s asset =
      (do let roots ← pair_trace.pair_empty_roots
          ok (returned roots input out rec chg s asset)) := by
  change (do let roots ← pair_trace.pair_empty_roots
             PV_Src_RecordReference.call roots input out rec chg s asset) = _
  simp only [reference_call]

#print axioms reference_call
#print axioms call
end R1Z.PV_Src_DynamicCallEquation
