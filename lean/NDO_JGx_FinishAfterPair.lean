import NDO_JGv_Pair
import NDO_JGo_TX2_FinishPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_FinishAfterPair
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1Stage2.Stage2Finish
/-- The actual dot and its comparison remain executable, including rejection. -/
def remaining (a : verifier.Accumulator) : Result (core.result.Result Unit verifier.Error) := do
  let r ← SAG_DotClosed.source (JFw_Frames.window 8007 2048) a.weights.deref
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue dot => do
    if a.next != 22#usize then ok (.Err verifier.Error.Query)
    else do
      let different ← Port3_FinishStage.ne dot a.rhs
      if different then ok (.Err verifier.Error.Query)
      else ok (.Ok ())
  | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame verifier.Error) residual
/-- Removes the Pair gate by its constructed execution; no dot success assumed. -/
theorem source (seed : FinishOps FIo_Install.W) (inactive : E) (a : verifier.Accumulator) :
    Port4D_FinishInstall.finish (FIo_Install.finishOps (.Ok ()) seed)
      (JGo_TX2_FinishPrefix.view inactive) JFo_Prepared.value a none=
    Port3_QueryInstall.result (remaining a) := by
  rw [JGo_TX2_FinishPrefix.installed]
  apply congrArg Port3_QueryInstall.result
  unfold JGo_TX2_FinishPrefixTools.remaining remaining
  simp only [Port4D_Round.native,Port3_FinishStage.native,Port3_FinishStage.release,
    FIo_Install.finishOps,FIn_WeightsInstall.install,FIn_Install.finishOps,SAG_StageScale.install,
    JGo_TX2_FinishPrefix.view,JGv_Pair.source,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry,Port3_FinishStage.ne,ne_eq,eq_self,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,
    Port3_QueryStage.mark]
  rfl
#print axioms source
end AspisR1.JGx_FinishAfterPair
end
