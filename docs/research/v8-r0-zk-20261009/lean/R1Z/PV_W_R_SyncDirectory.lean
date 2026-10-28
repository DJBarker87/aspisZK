import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_SyncDirectory
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (directory : std.path.Path) :
  P (core.result.Result Unit std.io.error.Error) := do
  let r ← perform (.base (.fileOpen (fun dictionary => letI : ExternalFuns := dictionary; (Shared0T.Insts.CoreConvertAsRef
std.path.Path.Insts.CoreConvertAsRefPath)) directory))
  let cf ← invoke "core.result.Result.Insts.CoreOpsTry.branch" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    perform (.base (.fileSync val))
  | core.ops.control_flow.ControlFlow.Break residual =>
    invoke "core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual" (fun ops =>
      letI : ExternalFuns := ops
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame std.io.error.Error) residual)

theorem erase_program (ops : ExternalFuns)
  (directory : std.path.Path) :
  erase ops (program directory) =
    @aspis_prover.state_only_entropy.sync_directory _ ops directory := by
  unfold program aspis_prover.state_only_entropy.sync_directory
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_perform ops _
  · intro r
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro cf
      try dsimp only
      cases cf with
      | Continue val =>
        exact erase_perform ops _
      | Break residual =>
        exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_SyncDirectory
