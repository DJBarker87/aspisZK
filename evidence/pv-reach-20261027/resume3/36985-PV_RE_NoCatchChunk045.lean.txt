import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix069
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


end R1Z.PV_RE_NoCatchSuffix069
pv_no_catch_binds ProverRwFull.prover.append_node_slots
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix069.continueAfter
