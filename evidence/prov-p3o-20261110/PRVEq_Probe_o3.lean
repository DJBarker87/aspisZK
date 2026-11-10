import Aeneas
import NNH_Tx2SourceConfiguration
import NNH_CorrectConfiguration
import PRVEq_AdapterStage1_o1
open Aeneas Aeneas.Std AspisR1
set_option autoImplicit false
noncomputable section
#check @DrvC_Installation.currentInstalled
#check @DrvC_Installation.current
#check @NNH_CorrectConfiguration.residual
#print NNH_CorrectConfiguration.residual
#check @RowShape_InstalledSlots.verifierOps
#print AdapterRw.SolanaDigest
open Lean Elab Command Meta in
elab "#whnfp " t:term : command => liftTermElabM do
  let e ← Term.elabTerm t none
  let e ← instantiateMVars e
  let r ← whnfD e
  logInfo m!"{r}"
section
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
#whnfp (NNH_CorrectConfiguration.sdk m env err r).op42
#whnfp (NNH_CorrectConfiguration.sdk m env err r).op43
#whnfp (NNH_CorrectConfiguration.sdk m env err r).op21
#whnfp (NNH_CorrectConfiguration.sdk m env err r).op53
end
