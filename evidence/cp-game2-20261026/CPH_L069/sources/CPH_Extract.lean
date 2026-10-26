import Lean
import Rc2_Top
set_option autoImplicit false
open Lean Meta Elab Tactic

/-- Proof refactoring only: inline the two checked root theorem bodies, select
source conjuncts, and require every unprovided legacy argument to disappear.
The resulting ordinary Lean term is kernel checked. No fact is admitted. -/
elab "cph_extract_rc2_source" : tactic => do
  let root ← mkConstWithFreshMVarLevels ``AspisR1.Rc2_Top.deployed
  let info ← getConstInfo ``AspisR1.Rc2_Top.deployed
  let some rootBody := info.value? true | throwError "Root has no checked body"
  let nextInfo ← getConstInfo ``AspisR1.T2R_Top.deployed
  let some nextBody := nextInfo.value? true | throwError "Predecessor has no checked body"
  let body := rootBody.replace fun e =>
    if e.isConstOf ``AspisR1.T2R_Top.deployed then
      some (nextBody.instantiateLevelParams nextInfo.levelParams e.constLevels!)
    else none
  let mut proof := body.instantiateLevelParams info.levelParams root.constLevels!
  let mut ty ← inferType root
  let lctx ← getLCtx
  while ty.isForall do
    let .forallE n d b _ := ty | unreachable!
    let localArg := lctx.foldl (init := none) fun found decl =>
      if decl.userName == n then some decl.toExpr else found
    let arg ← match localArg with
      | some e => pure e
      | none => mkFreshExprMVar d
    proof := mkApp proof arg
    ty := b.instantiate1 arg
  let mut parts : Array Expr := #[]
  for i in [:6] do
    let p ← withTransparency .reducible (whnf proof)
    unless p.getAppFn.isConstOf ``And.intro do
      throwError "Expected root conjunction at {i}: {p}"
    let args := p.getAppArgs
    parts := parts.push args[2]!
    proof := args[3]!
  parts := parts.push proof
  -- Rc2: driver, dictionary, obsolete headline, source, copy, events, protection.
  let kept := #[parts[0]!,parts[1]!,parts[3]!,parts[4]!,parts[5]!,parts[6]!]
  let mut out := kept[5]!
  for i in [0:5] do
    out ← mkAppM ``And.intro #[kept[4-i]!,out]
  out ← instantiateMVars out
  if out.hasMVar then throwError "A legacy argument remains in the source proof"
  let goal ← getMainGoal
  goal.assign out
  replaceMainGoal []
