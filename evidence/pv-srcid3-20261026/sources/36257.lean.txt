import R1Z.PV_Src_CheckedVariants
import R1Z.PV_Src_Fixture_CanonicalFixtures

/-! The two release fixture witnesses survive the selected-input Checked
stage. This is native carrier non-vacuity, not a successful full compiler run
or an installation of the supplied snapshot/compilation parameters. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CheckedFixtures
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort.pool_v1 PV_Src_CheckedEncoding
open PV_Src_Fixture_FixtureRecords

def transferInput (p : BuilderPublicProjection.Transfer) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :=
  input (witness false) (transferRequest p (witness false)) index snapshot compiled laneAnchor

def withdrawalInput (p : BuilderPublicProjection.Withdrawal) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :=
  input (witness true) (withdrawalRequest p (witness true)) index snapshot compiled laneAnchor

theorem transfer_checked (p : BuilderPublicProjection.Transfer) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    PV_Src_RecordReference.Checked (transferInput p index snapshot compiled laneAnchor) :=
  PV_Src_CheckedVariants.transfer_checked _ _ _ _ _ _

theorem withdrawal_checked (p : BuilderPublicProjection.Withdrawal) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    PV_Src_RecordReference.Checked (withdrawalInput p index snapshot compiled laneAnchor) :=
  PV_Src_CheckedVariants.withdrawal_checked _ _ _ _ _ _

theorem both_inhabited (p : BuilderPublicProjection.Transfer) (q : BuilderPublicProjection.Withdrawal)
    (index : U32) (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    Nonempty {i : PV_Src_NativeInput.Input // PV_Src_RecordReference.Checked i} ∧
      Nonempty {i : PV_Src_NativeInput.Input // PV_Src_RecordReference.Checked i} :=
  ⟨⟨⟨transferInput p index snapshot compiled laneAnchor,transfer_checked p index snapshot compiled laneAnchor⟩⟩,
    ⟨⟨withdrawalInput q index snapshot compiled laneAnchor,withdrawal_checked q index snapshot compiled laneAnchor⟩⟩⟩

#print axioms transfer_checked
#print axioms withdrawal_checked
#print axioms both_inhabited
end R1Z.PV_Src_CheckedFixtures
