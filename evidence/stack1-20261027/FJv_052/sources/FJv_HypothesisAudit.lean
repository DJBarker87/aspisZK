import FJv_Deployed
import FJu_Top
import Lean
open Lean Meta Elab
/- Exact leaf transformations: delete only a named implication antecedent. -/
run_meta do
  for (oldName,newName,binder) in [
      (``AspisR1.FJu_Finish.Outcome,``AspisR1.FJv_Finish.Outcome,`pairing_S3_S5_S9),
      (``AspisR1.FJv_Finish.Outcome,``AspisR1.FJv_DFinish.Outcome,`semantic_S3_S9)] do
    let old ← getConstInfo oldName
    let fresh ← getConstInfo newName
    let some before := old.value? true | throwError "Missing old leaf"
    let some after := fresh.value? true | throwError "Missing new leaf"
    let candidate ← mkConstWithFreshMVarLevels newName
    unless ← isDefEq (← inferType candidate) old.type do throwError "Leaf carrier changed"
    let candidate ← instantiateMVars candidate
    let after := after.instantiateLevelParams fresh.levelParams candidate.constLevels!
    let seen ← IO.mkRef (0 : Nat)
    before.forEach fun e => do
      if let .forallE n _ _ _ := e then
        if n == binder then seen.modify (· + 1)
    unless (← seen.get) == 1 do throwError "Expected exactly one named HYPOTHESIS"
    let dropped := before.replace fun e => match e with
      | .forallE n _ body _ => if n == binder then some (body.instantiate1 (.const ``True.intro [])) else none
      | _ => none
    unless ← withTransparency .reducible (isDefEq dropped after) do
      throwError "Leaf changed beyond the named hypothesis removal"
    logInfo m!"HYPOTHESIS ONLY: {oldName} -> {newName}: {binder}; conclusion and all witnesses identical"
  for (declName,expectedCount) in [(``AspisR1.FJu_Top.deployed,1),(``AspisR1.FJv_Top.deployed,1),(``AspisR1.FJv_Deployed.deployed,0)] do
    let info ← getConstInfo declName
    let seen ← IO.mkRef (0 : Nat)
    info.type.forEach fun e => do
      if let .forallE n _ _ _ := e then
        if n == `finishOwners then seen.modify (· + 1)
    unless (← seen.get) == expectedCount do throwError "Wrong global HYPOTHESIS count"
    logInfo m!"GLOBAL HYPOTHESIS COUNT: {declName}: {expectedCount}"
#print axioms AspisR1.FJv_Top.deployed
#print axioms AspisR1.FJv_Deployed.deployed
