import NNH_CommonSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Tx2SlotTransport
open Aeneas Aeneas.Std Result VTop_Stages
variable (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
abbrev stage := DrvC_Installation.stage (NNH_CorrectConfiguration.configuration missing env err reserve)

theorem geometry_slot (q : Array U32 22#usize) (start finish : Usize) :
 (stage missing env err reserve).op11 q start finish =
 Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install
  (NNH_CorrectConfiguration.configuration missing env err reserve).geometry)
  q start finish := by
 rfl

theorem finish_slot (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) :
 (stage missing env err reserve).op19 v p a none =
 Port4D_FinishInstall.finish (IDa_Deployed.finish reserve) v p a none := by
 rfl
#print axioms geometry_slot
#print axioms finish_slot
open Lean in
run_cmd do
 let env ← getEnv
 for (n,info) in env.constants.toList do
  let s := n.toString
  if s.startsWith "NLB_Parent." && !s.contains "._" then
   match info with
   | .thmInfo _ => logInfo m!"{n}: {info.type}"
   | _ => pure ()
#print AspisR1.SAQ_GeometrySource.install
end AspisR1.NNH_Tx2SlotTransport
end
