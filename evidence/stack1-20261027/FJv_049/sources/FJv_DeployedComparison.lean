import FJv_Deployed
import FJv_Specialised
import Lean
open Lean Meta Elab
run_meta do
  let old ← getConstInfo ``AspisR1.FJv_Specialised.deployed
  let fresh ← getConstInfo ``AspisR1.FJv_Deployed.deployed
  unless old.levelParams.length == fresh.levelParams.length do throwError "Universe count changed"
  let levels := old.levelParams.map Level.param
  let before := old.type.instantiateLevelParams old.levelParams levels
  let after := fresh.type.instantiateLevelParams fresh.levelParams levels
  let dropped := before.replace fun e => match e with
    | .forallE n _ body _ => if n == `finishOwners then some (body.instantiate1 (.const ``True.intro [])) else none
    | _ => none
  let canon := after.replace fun e =>
    if e.isConstOf ``AspisR1.FJv_DResult.Outcome then
      some (.const ``AspisR1.FJv_Result.Outcome e.constLevels!) else none
  unless dropped == canon do throwError "Specialised kernel type changed beyond global/native L146 removals"
  logInfo "SPECIALISED KERNEL ROOT: identical after deleting only finishOwners and changing native Outcome"
  let pairs := [
    (``AspisR1.FJv_Result.Outcome, ``AspisR1.FJv_DResult.Outcome, ``AspisR1.FJv_Caller.Outcome, ``AspisR1.FJv_DBoundCaller.Outcome),
    (``AspisR1.FJv_Caller.Outcome, ``AspisR1.FJv_DBoundCaller.Outcome, ``AspisR1.FJv_Cont.Outcome, ``AspisR1.FJv_DCont.Outcome),
    (``AspisR1.FJv_Cont.Outcome, ``AspisR1.FJv_DCont.Outcome, ``AspisR1.FJv_Literal.Outcome, ``AspisR1.FJv_DLiteral.Outcome),
    (``AspisR1.FJv_Literal.Outcome, ``AspisR1.FJv_DLiteral.Outcome, ``AspisR1.FJv_Finish.Outcome, ``AspisR1.FJv_DFinish.Outcome)]
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
  logInfo "Terminal hypothesis removed only at the leaf; all intervening native wrappers preserved"
