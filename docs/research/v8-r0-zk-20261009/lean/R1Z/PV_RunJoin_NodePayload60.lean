import R1Z.PV_RunJoin_ActualPlanSources59
import R1Z.PV_RunJoin_NodeSlot41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodePayload60
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact payload stage, factored before padding, with the original Option
conversion and all of its failure/divergence behavior retained. -/
def payload (cc1 cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
    (queries : Array U32 22#usize) (batch t : Usize) := do
  let idx ← prover.publication_indices queries (if batch=0#usize then 0#usize else compact.SPLIT)
    (if batch=0#usize then compact.SPLIT else 22#usize) (t=2#usize)
  let nodes ← match t.val with
    | 0 => host_commitment.Commitment.multiproof cc1 (alloc.vec.Vec.deref idx)
    | 1 => host_commitment.Commitment.multiproof cc2 (alloc.vec.Vec.deref idx)
    | _ => host_tree.BinaryTree.multiproof tree (alloc.vec.Vec.deref idx)
  core.option.Option.ok_or nodes verifier.Error.Allocation

theorem actual (p : prover.Publication) (batch t : Usize)
    (cc1 cc2 : host_commitment.Commitment)
    (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2) :
    PV_RunJoin_ActualPlanSources59.nodeBytes p batch t=payload cc1 cc2 p.tree p.queries batch t := by
  simp only [PV_RunJoin_ActualPlanSources59.nodeBytes,hc1,hc2,core.option.Option.unwrap,bind_tc_ok]
  rfl

/-- A single source slot first obtains exactly the cached model payload. -/
theorem source (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (tree : host_tree.BinaryTree) (queries : Array U32 22#usize) (batch t : Usize) :
    prover.append_node_slot out cc1 cc2 tree queries batch t=
      (do let r ← payload cc1 cc2 tree queries batch t
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue nodes => do
            let caps ← compact.SLOT_NODES
            let i := Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) t
            let size ← Array.index_usize caps i
            let next ← PV_RunJoin_NodeTail41.finish out nodes (Usize.wrapping_mul 32#usize size)
            ok (.Ok next)
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual) := by
  rw [PV_RunJoin_NodeSlot41.source]
  unfold PV_RunJoin_NodeSlot41.run payload
  by_cases hb : batch=0#usize <;> simp only [hb,if_true,if_false,bind_assoc_eq,bind_tc_ok,lift]

#print axioms actual
#print axioms source
end R1Z.PV_RunJoin_NodePayload60
