import GExp_CountLaws
import GExp_FirstCode
set_option autoImplicit false
namespace AspisR1.GExp_CountLaws
open Lean Meta Elab Tactic

/-- Supply the existing, fully typed first child and continuation explicitly.
This avoids higher-order guessing through the recursive Code.bind definition.
The resulting ordinary bind-budget proof is still checked by the kernel. -/
private def applyBudget (cost : Nat) (expected : Option Name) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``count 3 do throwError "expected bounded goal"
  let total := target.getAppArgs[1]!
  let tree ← zetaReduce target.getAppArgs[2]! (zetaDelta := false)
  let args := tree.getAppArgs
  let headName := tree.getAppFn.constName?
  let (child,continuation) ←
    if headName == some ``CheckpointBytes5Effect.bind || headName == some ``Bind.bind then
      pure (args[args.size-2]!,args[args.size-1]!)
    else if headName == some ``CheckpointBytes5Effect.Code.read then
      let parts := args[args.size-2]!
      let child ← mkAppM ``CheckpointBytes5Effect.read #[parts]
      pure (child,args[args.size-1]!)
    else throwError "expected Code bind/digest, found {tree.getAppFn}"
  let child ← withTransparency .reducible (whnf child)
  if let some fnName := expected then
    unless child.getAppFn.constName? == some fnName do
      throwError "unexpected child {child.getAppFn}, expected {fnName}"
  let term ← mkAppOptM ``then_count
    #[none,none,some child,some continuation,some total,some (mkNatLit cost)]
  replaceMainGoal (← goal.apply term)
elab "query_count_then " cost:num : tactic => applyBudget cost.getNat none
elab "query_count_then_for " cost:num child:ident : tactic => do
  let fnName ← resolveGlobalConstNoOverload child
  applyBudget cost.getNat (some fnName)
#print axioms then_count
end AspisR1.GExp_CountLaws
