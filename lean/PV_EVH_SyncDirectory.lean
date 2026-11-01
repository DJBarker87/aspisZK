import PV_EVH_NonceWorld
import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_SyncDirectory
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where

structure Compatible (c : Callees) : Prop where

def run
  (directory : std.path.Path) (fileAnswers : PV_EVH_NonceWorld.Answers) (c : Callees) : PV_EVH_Prefix.P (core.result.Result Unit std.io.error.Error) := do
  let r ← PV_EVH_Prefix.ofM (PV_EVH_NonceWorld.openFile fileAnswers (Shared0T.Insts.CoreConvertAsRef std.path.Path.Insts.CoreConvertAsRefPath) directory)
  let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    PV_EVH_Prefix.ofM (PV_EVH_NonceWorld.sync fileAnswers val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame std.io.error.Error) residual)

theorem run_fixed
  (directory : std.path.Path) (fileAnswers : PV_EVH_NonceWorld.Answers) (c : Callees) (compatible : Compatible c) (files_same : PV_EVH_NonceWorld.Compatible fileAnswers) :
    FinishedView (run directory fileAnswers c) (aspis_prover.state_only_entropy.sync_directory directory) := by
  unfold run aspis_prover.state_only_entropy.sync_directory
  try dsimp only
  apply PV_EVH_Prefix.bind_fixed
  ·
    exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceWorld.open_fixed fileAnswers _ _ (fun w => files_same.openFile _ _ w))
  · intro r
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact PV_EVH_Prefix.lift_fixed _
    · intro cf
      try dsimp only
      cases cf with
      | Continue val =>
        exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceWorld.sync_fixed fileAnswers _ (fun w => files_same.sync w _))
      | Break residual =>
        exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_SyncDirectory
