import R1Z.PV_RunJoin_NodeTail41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodeSlot41
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Source factorization only. All actual index, tree and commitment helpers,
including their errors and divergence, are kept verbatim. -/
def run
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize) (batch : Std.Usize) (t : Std.Usize) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  let begin1 ← if batch = 0#usize
                 then ok 0#usize
                 else ok compact.SPLIT
  let end1 ← if batch = 0#usize
               then ok compact.SPLIT
               else ok 22#usize
  let idx ← prover.publication_indices queries begin1 end1 (t = 2#usize)
  let o ←
    match t.val with
    | 0 =>
      let s := alloc.vec.Vec.deref idx
      host_commitment.Commitment.multiproof cc1 s
    | 1 =>
      let s := alloc.vec.Vec.deref idx
      host_commitment.Commitment.multiproof cc2 s
    | _ =>
      let s := alloc.vec.Vec.deref idx
      host_tree.BinaryTree.multiproof tree s
  let r ← core.option.Option.ok_or o verifier.Error.Allocation
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let a ← compact.SLOT_NODES
    let i ← Aeneas.Std.lift (Std.Usize.wrapping_mul 3#usize batch)
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add i t)
    let i2 ← Array.index_usize a i1
    let cap ← Aeneas.Std.lift (Std.Usize.wrapping_mul 32#usize i2)
    let result ← PV_RunJoin_NodeTail41.finish out val cap
    ok (core.result.Result.Ok result)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

/-- The proven padding tail occupies exactly the actual emitted slot tail.
This equation does not establish native multiproof/helper association. -/
theorem source (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment)
    (tree : host_tree.BinaryTree) (queries : Array U32 22#usize) (batch t : Usize) :
    prover.append_node_slot out cc1 cc2 tree queries batch t =
      run out cc1 cc2 tree queries batch t := by
  unfold prover.append_node_slot run PV_RunJoin_NodeTail41.finish
  simp only [bind_assoc_eq,bind_tc_ok,lift]
  rfl
#print axioms source
end R1Z.PV_RunJoin_NodeSlot41
