import R1Z.PV_Src_RootHelper
import R1Z.PV_Src_RecordDynamicResult
set_option autoImplicit false
namespace R1Z.PV_Src_RecordRootClosed
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput

theorem call (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    @PV_Src_RecordDynamic.call PV_Src_ExternalReference.dictionary input out rec chg s asset =
      PV_Src_RecordReference.call PV_Src_CanonicalRoots.table input out rec chg s asset := by
  rw [PV_Src_RecordDynamic.call,PV_Src_RootHelper.source]
  rfl

#print axioms call
end R1Z.PV_Src_RecordRootClosed
