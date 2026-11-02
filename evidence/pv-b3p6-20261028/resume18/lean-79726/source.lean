import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OracleBridge38
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Terminal :=
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
  Array (Array aspis_core.field.QM31 29#usize) 3#usize →
  Array aspis_core.field.QM31 10#usize →
  aspis_core.state_only_prefix.r0.Challenges →
  Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)

/-- Source continuation with an explicit terminal reference. All error layers,
actual caller claims, mask call, eta product and extra column remain in order.
This is a conditional source bridge, not a security-oracle identification. -/
def withTerminal [ExternalFuns]
  (terminal : Terminal)
  (self : host_semantic.SemanticOracle)
  (point : Array aspis_core.field.QM31 10#usize) :
  Result (core.result.Result aspis_core.field.QM31 r1_wire.Error)
  := do
  let r ← host_semantic.point_claims self.columns point
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      terminal
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


/-- The only hypothesis is op227's complete selected-callback law at the
actual public, claims, point and retained challenges. No success-only terminal
law or zero-claims substitution is sufficient. No use of this conditional law
is credited as closing op227 or the security-model bridge. -/
theorem selected_callback (ops : ExternalFuns) (terminal : Terminal)
    (self : host_semantic.SemanticOracle)
    (point : Array aspis_core.field.QM31 10#usize)
    (op227 : ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges) :
    @host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate
      _ ops self point = @withTerminal _ ops terminal self point := by
  unfold host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate withTerminal
  apply congrArg (Aeneas.Std.bind (@host_semantic.point_claims _ ops self.columns point))
  funext r
  apply congrArg (Aeneas.Std.bind (core.result.Result.Insts.CoreOpsTry.branch r))
  funext cf
  cases cf with
  | Break residual => rfl
  | Continue claims =>
    simp only [aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31,
      op227 claims]
    rfl

#print axioms selected_callback
end R1Z.PV_RunJoin_OracleBridge38
