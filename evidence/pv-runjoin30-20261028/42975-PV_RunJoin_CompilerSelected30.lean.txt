import R1Z.PV_RunJoin_ForestEquality30
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompilerSelected30
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

theorem selected [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records selected, pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot publicInput.asset = ok records ∧
      pair_tree_profile.PoolV1PairLeafWitnessV1.selected_commitment input.pair.pair_leaf input.pair.selected_second = ok selected ∧
      pair_forest_copy_builder.CopyRecords.input_leaf records = ok selected := by
  unfold pair_forest_trace.compile_forest_from_copies at h
  pv_peel h with records hr
  pv_peel h with selected hs
  pv_peel h with leaf hl
  pv_peel h with mismatch hm
  cases mismatch with
  | true => cases h
  | false =>
    have he := PV_RunJoin_ForestEquality30.equal selected leaf hm
    exact ⟨records,selected,hr,hs,hl.trans (congrArg Result.ok he.symm)⟩
#print axioms selected
end R1Z.PV_RunJoin_CompilerSelected30
