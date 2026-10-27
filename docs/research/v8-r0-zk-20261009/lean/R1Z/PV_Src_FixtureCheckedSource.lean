import R1Z.PV_Src_FixtureValidationInputs

/-! Checked for both release fixture carriers, using successful execution of
validate_common and the actual entry guards, not an unconditional mapper law. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_FixtureCheckedSource
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1
open PV_Src_CheckedFixtures PV_Src_AdmissionCommonSuccess

theorem transfer (p : BuilderPublicProjection.Transfer) (binding : Binding)
    (nullifier : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    PV_Src_RecordReference.Checked (transferInput p 0x54321#u32 snapshot compiled laneAnchor) := by
  have success := PV_Src_FixtureCommonValidation.common_success false binding nullifier
  have bounds := PV_Src_CheckedValidation.transfer_guards (600#u32 : U32) (400#u32 : U32) (by decide)
  apply PV_Src_CheckedValidation.checked_of_common_success
    (transferInput p 0x54321#u32 snapshot compiled laneAnchor) binding.pool binding.deployment_domain
    binding.anchor_sequence binding.anchor_root nullifier binding.asset_id (fresh binding)
  · rw [PV_Src_FixtureValidationInputs.transfer_pair]
    exact success
  · rw [(PV_Src_FixtureValidationInputs.transfer_values snapshot compiled laneAnchor p).1]
    exact bounds.1
  · rw [(PV_Src_FixtureValidationInputs.transfer_values snapshot compiled laneAnchor p).2]
    exact bounds.2
  · exact (PV_Src_CheckedFixtures.transfer_checked p 0x54321#u32 snapshot compiled laneAnchor).superRoot

theorem withdrawal (p : BuilderPublicProjection.Withdrawal) (binding : Binding)
    (nullifier : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    PV_Src_RecordReference.Checked (withdrawalInput p 0x54321#u32 snapshot compiled laneAnchor) := by
  have success := PV_Src_FixtureCommonValidation.common_success true binding nullifier
  have bounds := BuilderAdmissionCommon.common_facts binding.pool binding.deployment_domain
    binding.anchor_sequence binding.anchor_root nullifier binding.asset_id
    (PV_Src_FixturePairValidation.sourcePair true) (fresh binding) success
  have inputBound : (1000#u32 : U32).val < 2^30 := by
    simpa only [PV_Src_FixtureValidationInputs.input_value] using bounds.value_bound
  have out := PV_Src_CheckedValidation.withdrawal_conservation
    (1000#u32 : U32) (250#u32 : U32) (750#u32 : U32) inputBound (by decide)
  apply PV_Src_CheckedValidation.checked_of_common_success
    (withdrawalInput p 0x54321#u32 snapshot compiled laneAnchor) binding.pool binding.deployment_domain
    binding.anchor_sequence binding.anchor_root nullifier binding.asset_id (fresh binding)
  · rw [PV_Src_FixtureValidationInputs.withdrawal_pair]
    exact success
  · rw [(PV_Src_FixtureValidationInputs.withdrawal_values snapshot compiled laneAnchor p).1]
    exact out
  · rw [(PV_Src_FixtureValidationInputs.withdrawal_values snapshot compiled laneAnchor p).2]
    change 750 < 2^30
    decide
  · exact (PV_Src_CheckedFixtures.withdrawal_checked p 0x54321#u32 snapshot compiled laneAnchor).superRoot

#print axioms transfer
#print axioms withdrawal
end R1Z.PV_Src_FixtureCheckedSource
