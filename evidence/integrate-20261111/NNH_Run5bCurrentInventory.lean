import NNH_Run5bCurrentShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bCurrentInventory
open Aeneas Aeneas.Std Result
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
theorem adapter {H : Type} (D : AdapterRw.aspis_core.digest.Digest32 H)
 (sem : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (split : Usize) (hash : H) :
 (NNH_CorrectConfiguration.sdk m env err r).op10 D sem pub proof split hash none =
 AspisS6CurrentFirstInstallation.current (NNH_Run5bCurrentShape.current m env err r)
  D sem pub proof split hash none := rfl
#print axioms adapter
#print AspisS6CurrentFirstInstallation.current
#print AspisR1.RowShape_InstalledSlots.verifierOps
#print AspisR1CurrentCaller.Ops
open Lean in
run_cmd do
 let env ← getEnv
 for (n,ci) in env.constants.toList do
  let s := n.toString
  if ci.isTheorem && (s.startsWith "AspisR1CurrentCaller.BorrowedClaimPrepared." ||
   s.startsWith "OriginalPreparedNative." || s.startsWith "AspisR1CurrentCaller.InstalledPreparation.") then
   logInfo m!"{n}: {ci.type}"
end AspisR1.NNH_Run5bCurrentInventory
end
