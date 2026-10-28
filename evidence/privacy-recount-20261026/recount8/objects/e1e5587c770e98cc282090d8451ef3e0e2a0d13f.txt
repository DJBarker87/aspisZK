import R1Z.PV_RunJoin_AppendCapacity31
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LateSnapshot31
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22

theorem calls [ExternalLinear] (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (afterstate : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok afterstate)) :
    ∃ (roots : Roots) (tree next : incremental_merkle.IncrementalMerkleTreeV1)
      (receipt : incremental_merkle.AppendOneV1),
      pair_trace.pair_empty_roots = ok roots ∧
      incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots
        snapshot.next_pair_index snapshot.current_root snapshot.frontier roots = ok (.Ok tree) ∧
      incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots tree leaf roots = ok (.Ok (next,receipt)) := by
  unfold pair_forest_trace.late_append at h
  split at h
  · cases h
  · repeat' first
      | (have he := PV_RunJoin_DecoderReturn29.branch_continue _ _ hvalue; clear hvalue; cases he)
      | (have he := PV_RunJoin_ResultMap31.success _ _ _ _ hvalue; clear hvalue; cases he)
      | (have _result : core.result.Result _ _ := value; cases value <;> pv_head h)
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (cases h)
    all_goals exact ⟨_,_,_,_,by assumption,by assumption,by assumption⟩
#print axioms calls

theorem checked [ExternalLinear] (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (afterstate : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok afterstate)) :
    ∃ roots, pair_trace.pair_empty_roots = ok roots ∧
      PV_RunJoin_SnapshotRoot31.read
        ⟨snapshot.next_pair_index,snapshot.current_root,snapshot.frontier⟩ roots = ok (.Ok snapshot.current_root) := by
  obtain ⟨roots,tree,next,receipt,he,hc,ha⟩ := calls records snapshot leaf afterstate h
  have frame := PV_RunJoin_LateAppendFrame31.construct _ _ _ _ tree hc
  have valid := PV_RunJoin_RootConstructor31.validated _ _ _ _ tree hc
  obtain ⟨capacity,hcapacity,small⟩ := PV_RunJoin_AppendCapacity31.nonfull tree next leaf roots receipt ha
  have validTree : incremental_merkle.tree_reference.validate_owned tree roots = ok (.Ok ()) := by
    simpa only [frame] using valid
  have read := PV_RunJoin_SnapshotRoot31.checked tree roots capacity hcapacity small validTree
  exact ⟨roots,he,by simpa only [frame] using read⟩
#print axioms checked
end R1Z.PV_RunJoin_LateSnapshot31
