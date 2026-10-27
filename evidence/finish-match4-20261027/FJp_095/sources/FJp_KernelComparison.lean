import FJp_Top
import ARX_Root
import Lean
set_option autoImplicit false
open Lean Meta Elab
/- Mechanical comparison of the checked kernel types, without proof reduction. -/
run_meta do
  let old ← getConstInfo ``AspisR1.ARX_Root.deployed
  let fresh ← getConstInfo ``AspisR1.FJp_Top.deployed
  unless old.levelParams.length == fresh.levelParams.length do
    throwError "Root universe binder count changed"
  let levels := old.levelParams.map Level.param
  let before := old.type.instantiateLevelParams old.levelParams levels
  let after := fresh.type.instantiateLevelParams fresh.levelParams levels
  let canon := after.replace fun e =>
    if e.isConstOf ``AspisR1.FJp_GlobalOwners.Owners then
      some (.const ``AspisR1.FIp_GlobalOwners.Owners e.constLevels!)
    else if e.isConstOf ``AspisR1.FJp_Result.Outcome then
      some (.const ``AspisR1.FIs_Result.Outcome e.constLevels!)
    else none
  unless before == canon do
    throwError "Unexpected root kernel type change"
  logInfo "KERNEL ROOT TYPE: identical except the two named predicate replacements"
  let pairs := [
    (``AspisR1.FIs_Result.Outcome, ``AspisR1.FJp_Result.Outcome,
      ``AspisR1.FIs_Caller.Outcome, ``AspisR1.FJp_ActualCaller.Outcome),
    (``AspisR1.FIs_Caller.Outcome, ``AspisR1.FJp_ActualCaller.Outcome,
      ``AspisR1.FIs_Cont.Outcome, ``AspisR1.FJp_ActualCont.Outcome),
    (``AspisR1.FIs_Cont.Outcome, ``AspisR1.FJp_ActualCont.Outcome,
      ``AspisR1.FIs_Literal.Outcome, ``AspisR1.FJp_NativeLiteral.Outcome),
    (``AspisR1.FIs_Literal.Outcome, ``AspisR1.FJp_NativeLiteral.Outcome,
      ``AspisR1.FIs_Finish.Outcome, ``AspisR1.FJp_Finish.Outcome),
    (``AspisR1.FIp_GlobalOwners.Owners, ``AspisR1.FJp_GlobalOwners.Owners,
      ``AspisR1.FIp_Remaining.Holds, ``AspisR1.FJp_Remaining.Holds)]
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
    unless before == canon do throwError "Changed wrapper body: {freshName}"
    logInfo m!"KERNEL PREDICATE BODY: {freshName} identical after exact child substitution"
  let old ← getConstInfo ``AspisR1.FIs_Finish.Outcome
  let fresh ← getConstInfo ``AspisR1.FJp_Finish.Outcome
  let some before := old.value? true | throwError "Missing old native body"
  let some after := fresh.value? true | throwError "Missing new native body"
  let candidate ← mkConstWithFreshMVarLevels fresh.name
  unless ← isDefEq (← inferType candidate) old.type do throwError "Predicate type changed"
  let candidate ← instantiateMVars candidate
  let after := after.instantiateLevelParams fresh.levelParams candidate.constLevels!
  let canon := before.replace fun e =>
    match e with
    | .forallE n _ body _ =>
      if n == `matches_S4_S7 then some (body.instantiate1 (mkConst ``True.intro)) else none
    | _ => none
  unless after == canon do throwError "Unexpected native finish change"
  logInfo "KERNEL NATIVE FINISH: identical after removing matches_S4_S7 binder"
  let old ← getConstInfo ``AspisR1.FIp_Remaining.Holds
  let fresh ← getConstInfo ``AspisR1.FJp_Remaining.Holds
  let some before := old.value? true | throwError "Missing old global body"
  let some after := fresh.value? true | throwError "Missing new global body"
  let candidate ← mkConstWithFreshMVarLevels fresh.name
  unless ← isDefEq (← inferType candidate) old.type do throwError "Predicate type changed"
  let candidate ← instantiateMVars candidate
  let after := after.instantiateLevelParams fresh.levelParams candidate.constLevels!
  let canon := before.replace fun e =>
    if e.isAppOfArity ``And 2 then
      let args := e.getAppArgs
      match args[0]! with
      | .forallE _ _ body _ =>
        if body.getAppFn.isConstOf ``AspisR1.MatchingSupport.match0 then some args[1]! else none
      | _ => none
    else none
  unless after == canon do throwError "Unexpected global remaining-family change"
  logInfo "KERNEL GLOBAL REMAINING: identical after removing the matching conjunction leaf"
