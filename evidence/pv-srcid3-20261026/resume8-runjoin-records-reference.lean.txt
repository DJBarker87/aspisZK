import R1Z.PV_Src_RecordDynamic

/-! Owned extraction adapter, with the same root helper at an arbitrary explicit
external dictionary. This is a reference equation only. The shipped/reference
association remains a separate P6 gate; this file does not install Records for
the shipped caller or assert compiler success. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RecordsReference
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

def dictionary (E : ExternalLinear) : Records := ⟨fun input out rec chg snapshot asset => do
  let empty ← @pair_trace.pair_empty_roots E
  let (w,p) ← AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder.records_reference.records_reference_with_roots
    (PV_Src_NativeDirections.reference input) out (rec.map PV_Src_RecordReference.note)
    (PV_Src_RecordReference.note chg) (PV_Src_RecordReference.snapshot snapshot) asset empty
  ok (PV_Src_RecordReference.witness w, PV_Src_RecordReference.publicRecord p)⟩

theorem call_eq_dynamic (E : ExternalLinear)
    (w : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    @Records.call (dictionary E) w out rec change snapshot asset =
      @PV_Src_RecordDynamic.call E w out rec change snapshot asset := rfl

#print axioms dictionary
#print axioms call_eq_dynamic
end R1Z.PV_RunJoin_RecordsReference
