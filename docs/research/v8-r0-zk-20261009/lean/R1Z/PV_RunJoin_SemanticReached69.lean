import R1Z.PV_RunJoin_Sequential64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticReached69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_Sequential64
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31
/-- Exact continuation after the source terminal call, including both errors. -/
def tail (self : host_semantic.SemanticOracle) (point : Array Q 10#usize)
    (val : Array (Array Q 29#usize) 3#usize)
    (r1 : core.result.Result Q aspis_core.state_only_prefix.r0.Error) :
    Result (core.result.Result Q r1_wire.Error) := do
  let r2 ←
    core.result.Result.map_err
      host_semantic.OracleSemanticOracle.evaluate.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      r1 ()
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let a ← Array.index_usize val 0#usize
    let mask ← host_semantic.claim_mask_value a point
    let q ← aspis_core.field.QM31.mul self.eta val1
    let q1 ← aspis_core.field.QM31.add mask q
    let q2 ← Array.index_usize point 8#usize
    let q3 ← Array.index_usize point 9#usize
    let q4 ← host_semantic.extra self.d q2 q3
    let q5 ← aspis_core.field.QM31.add q1 q4
    ok (core.result.Result.Ok q5)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual

/-- Factor at the actual point_claims output; no existential terminal input. -/
theorem reached (self : host_semantic.SemanticOracle) (point : Array Q 10#usize)
    (claims : Array (Array Q 29#usize) 3#usize)
    (hc : host_semantic.point_claims self.columns point=ok (.Ok claims)) :
    host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate self point=
      (do let status ← aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
            self.«public» claims point self.challenges
          tail self point claims status) := by
  simp only [host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate,
    hc,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl

/-- Reify the terminal on the exact source-reached arguments. This does not
assert success of the residual callback. -/
theorem plan {S F : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (self : host_semantic.SemanticOracle) (point : Array Q 10#usize)
    (claims : Array (Array Q 29#usize) 3#usize)
    (hc : host_semantic.point_claims self.columns point=ok (.Ok claims)) :
    execute runtime (.terminal self.«public» claims point self.challenges
      (fun status => .step (tail self point claims status) Plan.done)) world=
      (do let value ← host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate self point
          ok (value,world)) := by
  rw [reached self point claims hc]
  simp only [execute,bind_assoc_eq]

#print axioms tail
#print axioms reached
#print axioms plan
end R1Z.PV_RunJoin_SemanticReached69
