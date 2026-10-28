import R1Z.PV_RunJoin_LateSnapshot31
import R1Z.PV_RunJoin_NativeSnapshotAgreement32
set_option autoImplicit false
namespace R1Z.PV_RunJoin_AppendDeterminism32
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22

/-- Successful late append returns the exact source tree afterstate. The
record-dependent append-root check can reject, but cannot change that state. -/
theorem returned [ExternalLinear] (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (out : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok out)) :
    ∃ (roots : Roots) (tree next : incremental_merkle.IncrementalMerkleTreeV1)
      (receipt : incremental_merkle.AppendOneV1),
      pair_trace.pair_empty_roots = ok roots ∧
      incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots
        snapshot.next_pair_index snapshot.current_root snapshot.frontier roots = ok (.Ok tree) ∧
      incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots tree leaf roots = ok (.Ok (next,receipt)) ∧
      out = ⟨next.next_leaf_index,next.root,next.frontier⟩ := by
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
    all_goals exact ⟨_,_,_,_,by assumption,by assumption,by assumption,rfl⟩
#print axioms returned

theorem unique [ExternalLinear] (a b : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (outA outB : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (ha : pair_forest_trace.late_append a snapshot leaf = ok (.Ok outA))
    (hb : pair_forest_trace.late_append b snapshot leaf = ok (.Ok outB)) : outA=outB := by
  obtain ⟨ea,ta,na,ra,hea,hca,haa,hoa⟩ := returned a snapshot leaf outA ha
  obtain ⟨eb,tb,nb,rb,heb,hcb,hab,hob⟩ := returned b snapshot leaf outB hb
  have roots := Result.ok.inj (hea.symm.trans heb)
  cases roots
  have trees := core.result.Result.Ok.inj (Result.ok.inj (hca.symm.trans hcb))
  cases trees
  have nexts := core.result.Result.Ok.inj (Result.ok.inj (haa.symm.trans hab))
  have hn := congrArg (fun x => x.1) nexts
  change na = nb at hn
  rw [hoa,hob,hn]
#print axioms unique
end R1Z.PV_RunJoin_AppendDeterminism32
