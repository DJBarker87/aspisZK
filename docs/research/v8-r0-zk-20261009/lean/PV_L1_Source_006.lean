import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
import PV_L1_Source_005
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_006
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize) :
  Logged (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  let _ ← observe .publication 0 (ok ())
  let r ← PV_L1_Logged.lift (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize)
  let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← PV_L1_Logged.lift (prover.append_node_slot val cc1 cc2 tree queries 0#usize 1#usize)
    let cf1 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        PV_L1_Source_005.produce val1 cc1 cc2 tree queries 0#usize 2#usize
      let cf2 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r2)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r3 ←
          PV_L1_Source_005.produce val2 cc1 cc2 tree queries 1#usize 0#usize
        let cf3 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r4 ←
            PV_L1_Source_005.produce val3 cc1 cc2 tree queries 1#usize 1#usize
          let cf4 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r4)
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            PV_L1_Source_005.produce val4 cc1 cc2 tree queries 1#usize 2#usize
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

theorem complete_result
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize) :
  erase (produce out cc1 cc2 tree queries) = prover.append_node_slots out cc1 cc2 tree queries := by
  unfold produce prover.append_node_slots
  simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_005.complete_result]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_005.complete_result]
#print axioms complete_result
end PV_L1_Source_006
