import GExq_OuterGoodLaws
set_option autoImplicit false
namespace AspisR1.GExq_OuterGoodLaws
open Lean Meta Elab Tactic

private def applyGoodBind (expected : Name) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``GExq_OuterLower.Good 3 do throwError "expected Good goal"
  let hashv := target.getAppArgs[1]!
  let tree ← zetaReduce target.getAppArgs[2]! (zetaDelta := false)
  let args := tree.getAppArgs
  let headName := tree.getAppFn.constName?
  unless headName == some ``S2W_Trace.bind || headName == some ``Bind.bind do
    throwError "expected caller bind"
  let child := args[args.size-2]!
  let continuation := args[args.size-1]!
  unless child.getAppFn.constName? == some expected do throwError "unexpected child"
  let term ← mkAppOptM ``bind_good
    #[none,none,some hashv,some child,some continuation]
  replaceMainGoal (← goal.apply term)

elab "good_bind_for " child:ident : tactic => do
  applyGoodBind (← resolveGlobalConstNoOverload child)
end AspisR1.GExq_OuterGoodLaws
