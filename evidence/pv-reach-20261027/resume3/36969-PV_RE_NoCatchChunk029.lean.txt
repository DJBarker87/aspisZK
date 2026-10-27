import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix053
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_semantic.SemanticOracle) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (host_semantic.point_claims self.columns point)) : Result (core.result.Result aspis_core.field.QM31 r1_wire.Error) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        self.«public» val point self.challenges
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
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual


end R1Z.PV_RE_NoCatchSuffix053
pv_no_catch_binds ProverRwFull.host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix053.continueAfter
