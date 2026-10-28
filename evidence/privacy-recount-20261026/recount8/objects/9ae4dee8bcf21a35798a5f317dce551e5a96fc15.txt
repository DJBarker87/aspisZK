import R1Z.PV_RunJoin_CompilerDictionary16
set_option autoImplicit false
namespace R1Z.PV_RunJoin_HoistedCaller16
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 PV_RunJoin_ShippedExternal

/- The composition of the authorized caller hoist. The Rust caller boundary
is checked by source-freeze-audit.json; this is not a second caller extraction. -/
def call (i : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1) (out : U32)
    (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (snap : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    Result pair_forest_copy_builder.CopyRecords := do
  let empty ← @pair_trace.pair_empty_roots E_shipped
  let (w,p) ← @Records.call (PV_RunJoin_RecordsAdapter16.R_shipped empty) i out rec chg snap asset
  ok ⟨w,p⟩

theorem frozen (i : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1) (out : U32)
    (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (snap : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    call i out rec chg snap asset =
      @pair_forest_copy_builder.CopyRecords.new PV_RunJoin_CompilerDictionary16.shipped i out rec chg snap asset := by
  unfold call
  rw [show @pair_trace.pair_empty_roots E_shipped = ok PV_Src_CanonicalRoots.table from PV_Src_RootHelper.source]
  rfl

theorem original (i : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1) (out : U32)
    (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (snap : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    call i out rec chg snap asset =
      @pair_forest_copy_builder.CopyRecords.new (@PV_Src_RecordDynamic.dictionary E_shipped) i out rec chg snap asset := by
  rw [frozen,PV_RunJoin_CompilerDictionary16.dictionary]
#print axioms call
#print axioms frozen
#print axioms original
end R1Z.PV_RunJoin_HoistedCaller16
