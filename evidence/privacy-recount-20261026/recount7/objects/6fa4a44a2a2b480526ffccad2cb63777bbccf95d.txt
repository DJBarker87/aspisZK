import R1Z.PV_RunJoin_TreeValue16
import R1Z.PV_RunJoin_PathValues16
import R1Z.PV_RunJoin_PairLeafCheck16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathChecks16
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open pair_forest_copy_builder PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M
theorem pair_canonical : Canon8 PV_RunJoin_PairLeafCheck16.digest := by
  intro i hi; interval_cases i <;> decide

theorem pair_value : R0P.merkleRootAux (R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23)
    PV_RunJoin_FixtureRecords.path 1 = digK (K := M) PV_RunJoin_PairLeafCheck16.digest := by
  rw [PV_RunJoin_PathValues16.prefix_1]
  funext i; fin_cases i <;> rfl

theorem transfer_pair_raw : tree_cur_r transferWitness transferPublic 1#usize = ok PV_RunJoin_PairLeafCheck16.digest :=
  PV_RunJoin_TreeValue16.transfer 1#usize (by decide) PV_RunJoin_PairLeafCheck16.digest pair_canonical pair_value

theorem transfer_pair : CopyRecords.path_digest ⟨transferWitness,transferPublic⟩ 1#usize = ok PV_RunJoin_PairLeafCheck16.digest := by
  rw [CopyRecords.path_digest,transfer_pair_raw]
  with_unfolding_all rfl
#print axioms transfer_pair_raw
#print axioms transfer_pair

theorem withdrawal_pair_raw : tree_cur_r withdrawalWitness withdrawalPublic 1#usize = ok PV_RunJoin_PairLeafCheck16.digest :=
  PV_RunJoin_TreeValue16.withdrawal 1#usize (by decide) PV_RunJoin_PairLeafCheck16.digest pair_canonical pair_value

theorem withdrawal_pair : CopyRecords.path_digest ⟨withdrawalWitness,withdrawalPublic⟩ 1#usize = ok PV_RunJoin_PairLeafCheck16.digest := by
  rw [CopyRecords.path_digest,withdrawal_pair_raw]
  with_unfolding_all rfl
#print axioms withdrawal_pair_raw
#print axioms withdrawal_pair
#print axioms pair_canonical
#print axioms pair_value
theorem lane_canonical : Canon8 PV_RunJoin_FixtureArguments.laneAnchor := by
  intro i hi; interval_cases i <;> decide

theorem lane_value : R0P.merkleRootAux (R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23)
    PV_RunJoin_FixtureRecords.path 21 = digK (K := M) PV_RunJoin_FixtureArguments.laneAnchor := by
  rw [PV_RunJoin_PathValues16.prefix_21]
  funext i; fin_cases i <;> rfl

theorem transfer_lane_raw : tree_cur_r transferWitness transferPublic 21#usize = ok PV_RunJoin_FixtureArguments.laneAnchor :=
  PV_RunJoin_TreeValue16.transfer 21#usize (by decide) PV_RunJoin_FixtureArguments.laneAnchor lane_canonical lane_value

theorem transfer_lane : CopyRecords.path_digest ⟨transferWitness,transferPublic⟩ 21#usize = ok PV_RunJoin_FixtureArguments.laneAnchor := by
  rw [CopyRecords.path_digest,transfer_lane_raw]
  with_unfolding_all rfl
#print axioms transfer_lane_raw
#print axioms transfer_lane

theorem withdrawal_lane_raw : tree_cur_r withdrawalWitness withdrawalPublic 21#usize = ok PV_RunJoin_FixtureArguments.laneAnchor :=
  PV_RunJoin_TreeValue16.withdrawal 21#usize (by decide) PV_RunJoin_FixtureArguments.laneAnchor lane_canonical lane_value

theorem withdrawal_lane : CopyRecords.path_digest ⟨withdrawalWitness,withdrawalPublic⟩ 21#usize = ok PV_RunJoin_FixtureArguments.laneAnchor := by
  rw [CopyRecords.path_digest,withdrawal_lane_raw]
  with_unfolding_all rfl
#print axioms withdrawal_lane_raw
#print axioms withdrawal_lane
#print axioms lane_canonical
#print axioms lane_value
theorem anchor_canonical : Canon8 PV_RunJoin_RecordedTransfer.publicRecord.anchor_root := by
  intro i hi; interval_cases i <;> decide

theorem anchor_value : R0P.merkleRootAux (R0P.digestOf PV_RunJoin_FixtureHashModel.s_3_23)
    PV_RunJoin_FixtureRecords.path 24 = digK (K := M) PV_RunJoin_RecordedTransfer.publicRecord.anchor_root := by
  rw [PV_RunJoin_PathValues16.prefix_24]
  funext i; fin_cases i <;> rfl

theorem transfer_anchor_raw : tree_cur_r transferWitness transferPublic 24#usize = ok PV_RunJoin_RecordedTransfer.publicRecord.anchor_root :=
  PV_RunJoin_TreeValue16.transfer 24#usize (by decide) PV_RunJoin_RecordedTransfer.publicRecord.anchor_root anchor_canonical anchor_value

theorem transfer_anchor : CopyRecords.path_digest ⟨transferWitness,transferPublic⟩ 24#usize = ok PV_RunJoin_RecordedTransfer.publicRecord.anchor_root := by
  rw [CopyRecords.path_digest,transfer_anchor_raw]
  with_unfolding_all rfl
#print axioms transfer_anchor_raw
#print axioms transfer_anchor

theorem withdrawal_anchor_raw : tree_cur_r withdrawalWitness withdrawalPublic 24#usize = ok PV_RunJoin_RecordedTransfer.publicRecord.anchor_root :=
  PV_RunJoin_TreeValue16.withdrawal 24#usize (by decide) PV_RunJoin_RecordedTransfer.publicRecord.anchor_root anchor_canonical anchor_value

theorem withdrawal_anchor : CopyRecords.path_digest ⟨withdrawalWitness,withdrawalPublic⟩ 24#usize = ok PV_RunJoin_RecordedTransfer.publicRecord.anchor_root := by
  rw [CopyRecords.path_digest,withdrawal_anchor_raw]
  with_unfolding_all rfl
#print axioms withdrawal_anchor_raw
#print axioms withdrawal_anchor
#print axioms anchor_canonical
#print axioms anchor_value
end R1Z.PV_RunJoin_PathChecks16
