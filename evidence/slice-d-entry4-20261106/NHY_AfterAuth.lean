import NHJ_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace NHY_AfterAuth
open Aeneas Aeneas.Std Result
abbrev E := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Statement := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Reply := core.result.Result Unit E
abbrev Out := core.result.Result Unit PE

/-- Exact source tail after the authenticated child returns, before packet
substitution. Error callback and emission are distinct calls, in source order. -/
def tail (ops : AdapterRw.Ops) (statement : Statement) (reply : Reply) : Result Out := do
 let mapped ← AdapterRw.core.result.Result.map_err (BuiltinFnOnce E PE) reply ops.op44
 let cf ← core.result.Result.Insts.CoreOpsTry.branch mapped
 match cf with
 | .Continue _ => ops.op53 statement
 | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame PE) residual

theorem success (ops : AdapterRw.Ops) (statement : Statement) :
    tail ops statement (.Ok ()) = ops.op53 statement := rfl

theorem rejected (ops : AdapterRw.Ops) (statement : Statement) (error : E) :
    tail ops statement (.Err error) =
      (do let mapped ← ops.op44 error
          ok (.Err mapped : Out)) := by
  unfold tail AdapterRw.core.result.Result.map_err
  simp only [BuiltinFnOnce,bind_tc_ok]
  cases h : ops.op44 error <;> simp [h,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame]

/-- All outer failure/divergence possibilities are retained, not assumed away. -/
def after (ops : AdapterRw.Ops) (statement : Statement) (child : Result Reply) : Result Out :=
 child >>= tail ops statement

theorem child_error (ops : AdapterRw.Ops) (statement : Statement) (error : E) :
    after ops statement (ok (.Err error)) =
      (do let mapped ← ops.op44 error
          ok (.Err mapped : Out)) := by
  simp only [after,bind_tc_ok,rejected]

#print axioms success
#print axioms rejected
#print axioms child_error
end NHY_AfterAuth
