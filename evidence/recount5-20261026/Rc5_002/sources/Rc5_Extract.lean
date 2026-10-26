import Lean
import SAF_Deployed
set_option autoImplicit false
open Lean Meta Elab Tactic

/-- Proof refactoring only: inline the two checked root theorem bodies, select
source conjuncts, and require every unprovided legacy argument to disappear.
The resulting ordinary Lean term is kernel checked. No fact is admitted. -/
elab "rc5_extract_saf_source" : tactic => do
  let root ← mkConstWithFreshMVarLevels ``AspisR1.SAF_Deployed.deployed
  let info ← getConstInfo ``AspisR1.SAF_Deployed.deployed
  let some rootBody := info.value? true | throwError "Root has no checked body"
  let names := [``AspisR1.SAF_C_SAF_FinalTop.deployed,
    ``AspisR1.SAF_C_SAF_Top.deployed, ``AspisR1.SAF_C_Rc3_Top.deployed,
    ``AspisR1.SAF_C_SAP_LiteralTop.deployed]
  let mut body := rootBody
  for name in names do
    let ci ← getConstInfo name
    let some value := ci.value? true | throwError "Missing checked predecessor"
    body := body.replace fun e =>
      if e.isConstOf name then some (value.instantiateLevelParams ci.levelParams e.constLevels!)
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
  let kept := #[parts[0]!,parts[1]!,parts[3]!,parts[4]!,parts[5]!]
  let mut out := kept[4]!
  for i in [0:4] do
    out ← mkAppM ``And.intro #[kept[3-i]!,out]
  out ← instantiateMVars out
  if out.hasMVar then throwError "A legacy argument remains in the source proof"
  let goal ← getMainGoal
  goal.assign out
  replaceMainGoal []
