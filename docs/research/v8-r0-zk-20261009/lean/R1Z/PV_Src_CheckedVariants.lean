import R1Z.PV_Src_CheckedEncoding

/-! Both public request variants of the canonical carrier satisfy the exact
primitive selected-input condition, for arbitrary snapshots/returned data. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CheckedVariants
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort.pool_v1 PV_Src_CheckedEncoding

theorem transfer_checked (w : W) (p : BuilderPublicProjection.Transfer) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    PV_Src_RecordReference.Checked
      (input w (transferRequest p w) index snapshot compiled laneAnchor) :=
  checked w _ index snapshot compiled laneAnchor rfl

theorem withdrawal_checked (w : W) (p : BuilderPublicProjection.Withdrawal) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    PV_Src_RecordReference.Checked
      (input w (withdrawalRequest p w) index snapshot compiled laneAnchor) :=
  checked w _ index snapshot compiled laneAnchor rfl

#print axioms transfer_checked
#print axioms withdrawal_checked
end R1Z.PV_Src_CheckedVariants
