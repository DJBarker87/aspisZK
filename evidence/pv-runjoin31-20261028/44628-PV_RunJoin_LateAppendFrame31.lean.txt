import R1Z.PV_RunJoin_ResultMap31
import R1Z.PV_RunJoin_DecoderReturn29
import R1Z.PV_RunJoin_UniversalTreeFrame22
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LateAppendFrame31
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22

theorem returned [ExternalLinear]
    (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (afterstate : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok afterstate)) :
    ∃ (roots : Roots) (tree next : incremental_merkle.IncrementalMerkleTreeV1)
      (receipt : incremental_merkle.AppendOneV1),
      incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots
        snapshot.next_pair_index snapshot.current_root snapshot.frontier roots = ok (.Ok tree) ∧
      incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots tree leaf roots = ok (.Ok (next,receipt)) ∧
      afterstate.next_frontier = next.frontier := by
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
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
      | (cases h)
    all_goals exact ⟨_,_,_,_,by assumption,by assumption,rfl⟩
#print axioms returned

theorem construct [ExternalLinear] (index : U64) (root : Digest) (frontier : Frontier)
    (roots : Roots) (tree : incremental_merkle.IncrementalMerkleTreeV1)
    (h : incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots index root frontier roots = ok (.Ok tree)) :
    tree = ⟨index,root,frontier⟩ := by
  unfold incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots at h
  pv_peel h with made hmade
  cases made with
  | Err error => cases h
  | Ok owned =>
    have frame := PV_RunJoin_UniversalTreeFrame22.construct index root frontier roots owned hmade
    change (ok (.Ok owned.inner) : Result (core.result.Result _ _)) = ok (.Ok tree) at h
    cases core.result.Result.Ok.inj (Result.ok.inj h)
    exact frame.1
#print axioms construct
end R1Z.PV_RunJoin_LateAppendFrame31
