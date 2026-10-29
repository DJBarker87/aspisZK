import R1Z.PV_RunJoin_EmptyTree59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeNoSuccess59
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Only the tree is replaced. Lane/word/salt fields need no reduction. -/
def replaceTree (c : host_commitment.Commitment) : host_commitment.Commitment :=
  {c with tree := PV_RunJoin_EmptyTree59.empty}

theorem slot (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (tree : host_tree.BinaryTree) (queries : Array U32 22#usize)
    (depth : multiproof.LEAF_BITS=ok 18#u32) (next : alloc.vec.Vec U8) :
    prover.append_node_slot out (replaceTree cc1) cc2 tree queries 0#usize 0#usize ≠ ok (.Ok next) := by
  intro success
  unfold prover.append_node_slot at success
  simp only [if_true,bind_tc_ok] at success
  obtain ⟨idx,hidx,tail⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  obtain ⟨nodes,hnodes,tail⟩ := PV_RunJoin_ResultPost.bind_eq_ok tail
  cases nodes with
  | none => cases tail
  | some nodes =>
    exact PV_RunJoin_EmptyTree59.no_multiproof _ depth nodes hnodes

theorem slots (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (tree : host_tree.BinaryTree) (queries : Array U32 22#usize)
    (depth : multiproof.LEAF_BITS=ok 18#u32) (next : alloc.vec.Vec U8) :
    prover.append_node_slots out (replaceTree cc1) cc2 tree queries ≠ ok (.Ok next) := by
  intro success
  unfold prover.append_node_slots at success
  obtain ⟨first,hfirst,tail⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  cases first with
  | Err error => cases tail
  | Ok first => exact slot out cc1 cc2 tree queries depth first hfirst

theorem bytes_none (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (tree : host_tree.BinaryTree) (queries : Array U32 22#usize)
    (depth : multiproof.LEAF_BITS=ok 18#u32) :
    PV_RunJoin_PublishSkeleton54.resultBytes
      (prover.append_node_slots out (replaceTree cc1) cc2 tree queries)=none := by
  cases h : prover.append_node_slots out (replaceTree cc1) cc2 tree queries with
  | fail e => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err e => rfl
    | Ok next => exact False.elim (slots out cc1 cc2 tree queries depth next h)

#print axioms replaceTree
#print axioms slot
#print axioms slots
#print axioms bytes_none
end R1Z.PV_RunJoin_NodeNoSuccess59
