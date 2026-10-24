import S1PrepareBudgetCoreV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedBudget
open Lean Meta Elab Tactic

/-- Supply the existing, fully typed first child and continuation explicitly.
This avoids higher-order guessing through the recursive Code.bind definition.
The resulting ordinary bind-budget proof is still checked by the kernel. -/
elab "budget_then " cost:num : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``bounded 3 do throwError "expected bounded goal"
  let total := target.getAppArgs[1]!
  let tree := target.getAppArgs[2]!
  let args := tree.getAppArgs
  let name := tree.getAppFn.constName?
  let (child,continuation) ←
    if name==some ``PreparedHashCode.bind || name==some ``Bind.bind then
      pure (args[args.size-2]!,args[args.size-1]!)
    else if name==some ``PreparedHashCode.Code.digest then
      let dict := args[args.size-4]!
      let hash := args[args.size-3]!
      let parts := args[args.size-2]!
      let child ← mkAppM ``PreparedHashEffects.Effects.digest
        #[mkConst ``PreparedHashCode.effects,dict,hash,parts]
      pure (child,args[args.size-1]!)
    else throwError "expected Code bind/digest, found {tree.getAppFn}"
  let lemma ← mkAppOptM ``then_bound
    #[none,none,some child,some continuation,some total,some (mkNatLit cost.getNat)]
  replaceMainGoal (← goal.apply lemma)
end AspisR1PublicPreparation.PreparedBudget
