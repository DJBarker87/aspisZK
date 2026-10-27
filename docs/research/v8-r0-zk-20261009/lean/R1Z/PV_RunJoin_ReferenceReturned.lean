import R1Z.PV_RunJoin_ReferenceRootClosed

/-! Complete returned values of the extracted reference, with roots computed
by the checked source helper. This is not a shipped Records installation. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ReferenceReturned
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 PV_RunJoin_ShippedExternal

abbrev Input := pair_forest_trace.PoolV1PairForestInputNoteWitnessV1
abbrev Note := payment_relation.PoolV1OutputNoteWitnessV1
abbrev Snapshot := pair_tree_profile.PoolV1PairLiveSnapshotV1

def witness (w : Input) (out : U32) (rec : Option Note) (chg : Note) : pair_forest_copy_builder.RW :=
  PV_Src_RecordReference.witness (BuilderRecordsReference.witness
    (PV_Src_NativeDirections.reference w) out (rec.map PV_Src_RecordReference.note)
    (PV_Src_RecordReference.note chg))

def publicRecord (rec : Option Note) (s : Snapshot) (asset : U32) : pair_forest_copy_builder.RP :=
  PV_Src_RecordReference.publicRecord (BuilderRecordsReference.publicRecord
    (rec.map PV_Src_RecordReference.note) (PV_Src_RecordReference.snapshot s)
    asset PV_Src_CanonicalRoots.table)

theorem call (w : Input) (out : U32) (rec : Option Note) (chg : Note)
    (s : Snapshot) (asset : U32) :
    @Records.call (PV_RunJoin_RecordsReference.dictionary E_shipped) w out rec chg s asset =
      ok (witness w out rec chg,publicRecord rec s asset) := by
  rw [PV_RunJoin_ReferenceRootClosed.call]
  unfold PV_Src_RecordReference.call
  rw [BuilderRecordsReference.records]
  rfl

#print axioms witness
#print axioms publicRecord
#print axioms call
end R1Z.PV_RunJoin_ReferenceReturned
