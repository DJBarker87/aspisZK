import RPz7_GExp_Association
import RPz7_S1CurrentPrepareCodeExactV1
set_option autoImplicit false
namespace AspisR1.GExp_Association
open Lean Meta Elab Tactic
open AspisR1PublicPreparation
private def applyAssociation (expected : Option Name) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``SdkD_PrepareLower.Associated 3 do
    throwError "expected Associated goal"
  let hashv := target.getAppArgs[0]!
  let tree ← zetaReduce target.getAppArgs[2]! (zetaDelta := false)
  let args := tree.getAppArgs
  let headName := tree.getAppFn.constName?
  let (child,continuation) ←
    if headName == some ``PreparedHashCode.bind || headName == some ``Bind.bind then
      pure (args[args.size-2]!,args[args.size-1]!)
    else throwError "expected Code bind, found {tree.getAppFn}"
  let child ← withTransparency .reducible (whnf child)
  if let some fnName := expected then
    unless child.getAppFn.constName? == some fnName do
      throwError "unexpected child {child.getAppFn}, expected {fnName}"
  let term ← mkAppOptM ``bind_associated
    #[some hashv,none,none,some child,some continuation]
  replaceMainGoal (← goal.apply term)
elab "association_then" : tactic => applyAssociation none
elab "association_then_for " child:ident : tactic => do
  applyAssociation (some (← resolveGlobalConstNoOverload child))
end AspisR1.GExp_Association
