import R1Z.PV_Src_CheckedFixtures
import R1Z.PV_Src_BanksTotal

/-! Non-vacuity through every discharged primitive record/bank stage for the
canonical native encodings. Full forest entry success is not inferred. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CheckedPipeline
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1 PV_Src_NativeInput

theorem stages (roots : BuilderRecordsReference.Roots) (i : Input)
    (checked : PV_Src_RecordReference.Checked i) :
    ∃ records banks,
      @newRecords (PV_Src_RecordReference.withRoots roots) i = ok records ∧
      WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) := by
  let records := PV_Src_RecordReference.returned roots i
  have hr := PV_Src_RecordReference.newRecords_eq roots i
  obtain ⟨banks,hb⟩ := PV_Src_BanksTotal.banks_total records
  exact ⟨records,banks,hr,PV_Src_RecordReference.words roots i checked records hr,hb⟩

theorem transfer_stages (roots : BuilderRecordsReference.Roots)
    (p : BuilderPublicProjection.Transfer) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    ∃ records banks,
      @newRecords (PV_Src_RecordReference.withRoots roots)
        (PV_Src_CheckedFixtures.transferInput p index snapshot compiled laneAnchor) = ok records ∧
      WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) :=
  stages roots _ (PV_Src_CheckedFixtures.transfer_checked _ _ _ _ _)

theorem withdrawal_stages (roots : BuilderRecordsReference.Roots)
    (p : BuilderPublicProjection.Withdrawal) (index : U32)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (laneAnchor : Array U32 8#usize) :
    ∃ records banks,
      @newRecords (PV_Src_RecordReference.withRoots roots)
        (PV_Src_CheckedFixtures.withdrawalInput p index snapshot compiled laneAnchor) = ok records ∧
      WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness records.w) ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) :=
  stages roots _ (PV_Src_CheckedFixtures.withdrawal_checked _ _ _ _ _)

#print axioms stages
#print axioms transfer_stages
#print axioms withdrawal_stages
end R1Z.PV_Src_CheckedPipeline
