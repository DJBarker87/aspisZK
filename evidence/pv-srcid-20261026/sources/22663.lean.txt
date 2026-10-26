import R1Z.PV_Src_ForestBanks

/-! Successful forest compilation returns the very merged bank obtained from
its record object. Only the finite outer control flow is split: no hash,
recurrence cell, or validator computation is evaluated by this proof. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ForestCompilation
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderRecordsFields
open BuilderForestAdmissionPort.pool_v1

/-- Every successful path shares the record object and returned bank. -/
theorem returned_bank [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic)
    (anchor : Array aspis_core.field.M31 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records banks,
      pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot
        publicInput.asset = ok records ∧
      pair_forest_copy_builder.CopyRecords.banks records = ok (some banks) ∧
      compiled.semantic_c1.c1 = banks.merged := by
  unfold pair_forest_trace.compile_forest_from_copies at h
  obtain ⟨records,hr,h⟩ := bind_ok_inv h
  refine ⟨records,?_⟩
  all_goals
    repeat' first
      | obtain ⟨value,hvalue,h⟩ := bind_ok_inv h
      | split at h
      | contradiction
      | cases h
    all_goals simp_all only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame,bind_tc_ok]

#print axioms returned_bank
end R1Z.PV_Src_ForestCompilation
