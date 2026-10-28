import R1Z.PV_RunJoin_GeneralBranches16
import R1Z.PV_RunJoin_RecordsAdapter16
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalDictionary22
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_ArrayShapes16

theorem with_roots (empty : Array (Array U32 8#usize) 21#usize)
    (i : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (snap : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    @Records.call (PV_RunJoin_RecordsAdapter16.R_shipped empty) i out rec chg snap asset =
      PV_Src_RecordReference.call empty i out rec chg snap asset := by
  cases hs : i.pair.selected_second with
  | false =>
    cases rec with
    | none => exact PV_RunJoin_GeneralBranches16.none_first empty i out chg snap asset hs
    | some r => exact PV_RunJoin_GeneralBranches16.some_first empty i out r chg snap asset hs
  | true =>
    cases rec with
    | none => exact PV_RunJoin_GeneralBranches16.none_second empty i out chg snap asset hs
    | some r => exact PV_RunJoin_GeneralBranches16.some_second empty i out r chg snap asset hs

#print axioms with_roots
end R1Z.PV_RunJoin_UniversalDictionary22
