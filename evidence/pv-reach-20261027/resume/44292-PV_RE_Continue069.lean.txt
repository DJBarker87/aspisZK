import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue069
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.append_node_slots`.
Recursive calls remain the original extracted calls. -/
def continueAfter (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment) (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree) (queries : Array Std.U32 22#usize) (pvBoundValue : Payload (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize)) : Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  let r := pvBoundValue
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← prover.append_node_slot val cc1 cc2 tree queries 0#usize 1#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        prover.append_node_slot val1 cc1 cc2 tree queries 0#usize 2#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r3 ←
          prover.append_node_slot val2 cc1 cc2 tree queries 1#usize 0#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r4 ←
            prover.append_node_slot val3 cc1 cc2 tree queries 1#usize 1#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            prover.append_node_slot val4 cc1 cc2 tree queries 1#usize 2#usize
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment) (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree) (queries : Array Std.U32 22#usize) :
    prover.append_node_slots (out := out) (cc1 := cc1) (cc2 := cc2) (tree := tree) (queries := queries) =
      (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize >>= fun pvBoundValue => continueAfter (out := out) (cc1 := cc1) (cc2 := cc2) (tree := tree) (queries := queries) pvBoundValue) := by
  rw [prover.append_node_slots]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment) (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree) (queries : Array Std.U32 22#usize) (pvBoundValue : Payload (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize))
    (h : (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize) = .ok pvBoundValue) :
    prover.append_node_slots (out := out) (cc1 := cc1) (cc2 := cc2) (tree := tree) (queries := queries) = continueAfter (out := out) (cc1 := cc1) (cc2 := cc2) (tree := tree) (queries := queries) pvBoundValue := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment) (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree) (queries : Array Std.U32 22#usize) (e : Error)
    (h : (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize) = .fail e) :
    prover.append_node_slots (out := out) (cc1 := cc1) (cc2 := cc2) (tree := tree) (queries := queries) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment) (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree) (queries : Array Std.U32 22#usize)
    (h : (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize) = .div) :
    prover.append_node_slots (out := out) (cc1 := cc1) (cc2 := cc2) (tree := tree) (queries := queries) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue069
