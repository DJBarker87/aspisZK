import R1Z.PV_RunJoin_PairChecks29
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PairValidationReads31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
theorem leaf_validated [ExternalLinear]
    (leaf : pair_tree_profile.PoolV1PairLeafWitnessV1) (d : Array U32 8#usize)
    (h : pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest leaf = ok (.Ok d)) :
    leaf.validate = ok (.Ok ()) := by
  unfold pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest at h
  pv_peel h with result hr
  pv_peel h with flow hf
  cases flow with
  | Continue u =>
    cases u
    have he := PV_RunJoin_DecoderReturn29.branch_continue result () hf
    cases he
    exact hr
  | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
#print axioms leaf_validated
theorem compiler_validated [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change publicInput anchor snapshot = ok (.Ok compiled)) :
    input.pair.pair_leaf.validate = ok (.Ok ()) := by
  unfold pair_forest_trace.compile_forest_from_copies at h
  pv_peel h with records hr
  pv_peel h with selected hs
  pv_peel h with inputLeaf hi
  pv_peel h with mismatch hm
  cases mismatch <;> simp only [Bool.false_eq_true,↓reduceIte] at h
  · pv_peel h with pairDigest hp
    pv_peel h with result hl
    cases result with
    | Ok d => exact leaf_validated input.pair.pair_leaf d hl
    | Err e =>
      pv_peel h with mapped hmap
      unfold R1Z.BuilderForestStdPort.core.result.Result.map_err R1Z.BuilderAdmissionStd.mapErr at hmap
      pv_peel hmap with mappedError he
      cases Result.ok.inj hmap
      pv_peel h with flow hflow
      cases Result.ok.inj hflow
      exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
  · cases h
#print axioms compiler_validated
end R1Z.PV_RunJoin_PairValidationReads31
