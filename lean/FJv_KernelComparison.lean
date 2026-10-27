import FJu_Top
import FJv_Top
import Lean
set_option autoImplicit false
open Lean Meta Elab
/- Mechanical comparison of the checked kernel types, without proof reduction. -/
run_meta do
  let old ← getConstInfo ``AspisR1.FJu_Top.deployed
  let fresh ← getConstInfo ``AspisR1.FJv_Top.deployed
  unless old.levelParams.length == fresh.levelParams.length do
    throwError "Root universe binder count changed"
  let levels := old.levelParams.map Level.param
  let before := old.type.instantiateLevelParams old.levelParams levels
  let after := fresh.type.instantiateLevelParams fresh.levelParams levels
  let canon := after.replace fun e =>
    if e.isConstOf ``AspisR1.FJv_GlobalOwners.Owners then
      some (.const ``AspisR1.FJu_GlobalOwners.Owners e.constLevels!)
    else if e.isConstOf ``AspisR1.FJv_Result.Outcome then
      some (.const ``AspisR1.FJu_Result.Outcome e.constLevels!)
    else none
  unless before == canon do
    throwError "Unexpected root kernel type change"
  logInfo "KERNEL ROOT TYPE: identical except the two named predicate replacements"
  let pairs := [
    (``AspisR1.FJu_Result.Outcome, ``AspisR1.FJv_Result.Outcome, ``AspisR1.FJu_Caller.Outcome, ``AspisR1.FJv_Caller.Outcome),
    (``AspisR1.FJu_Caller.Outcome, ``AspisR1.FJv_Caller.Outcome, ``AspisR1.FJu_Cont.Outcome, ``AspisR1.FJv_Cont.Outcome),
    (``AspisR1.FJu_Cont.Outcome, ``AspisR1.FJv_Cont.Outcome, ``AspisR1.FJu_NativeLiteral.Outcome, ``AspisR1.FJv_Literal.Outcome),
    (``AspisR1.FJu_NativeLiteral.Outcome, ``AspisR1.FJv_Literal.Outcome, ``AspisR1.FJu_Finish.Outcome, ``AspisR1.FJv_Finish.Outcome),
]
  for (oldName,freshName,oldChild,freshChild) in pairs do
    let old ← getConstInfo oldName
    let fresh ← getConstInfo freshName
    let some before := old.value? true | throwError "Missing old predicate body"
    let some after := fresh.value? true | throwError "Missing new predicate body"
    let candidate ← mkConstWithFreshMVarLevels freshName
    unless ← isDefEq (← inferType candidate) old.type do
      throwError "Predicate type changed: {freshName}"
    let candidate ← instantiateMVars candidate
    let after := after.instantiateLevelParams fresh.levelParams candidate.constLevels!
    let childInfo ← getConstInfo freshChild
    let replacement ← mkConstWithFreshMVarLevels oldChild
    unless ← isDefEq (← inferType replacement) childInfo.type do
      throwError "Child predicate type changed: {freshChild}"
    let replacement ← instantiateMVars replacement
    let canon := after.replace fun e =>
      if e.isConstOf freshChild then
        some (replacement.instantiateLevelParams childInfo.levelParams e.constLevels!) else none
    if before == canon then
      logInfo m!"KERNEL PREDICATE BODY: {freshName} structurally identical after child substitution"
    else if ← withTransparency .reducible (isDefEq before canon) then
      logInfo m!"KERNEL PREDICATE BODY: {freshName} definitionally identical after child substitution"
    else
      let a := (reprStr before).toList
      let b := (reprStr canon).toList
      let n := ((a.zip b).takeWhile (fun p => p.1 == p.2)).length
      logInfo m!"FIRST DIFFERENCE old={String.ofList ((a.drop (n-80)).take 400)}"
      logInfo m!"FIRST DIFFERENCE new={String.ofList ((b.drop (n-80)).take 400)}"
      throwError "Changed wrapper body: {freshName}"
  logInfo "Pair removed only at the leaf; all intervening native wrappers preserved"
