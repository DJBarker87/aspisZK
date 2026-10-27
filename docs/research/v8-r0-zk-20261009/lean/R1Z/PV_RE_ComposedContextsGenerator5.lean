import R1Z.ProverRwFullFuns
import R1Z.PV_RE_SourceContexts
import R1Z.PV_RE_LiteralShape5
import Lean
open Lean Meta Elab Command Term
namespace R1Z.PV_RE_ComposedContextsGenerator5

/-- Remove administrative lets only. Do not unfold callees or fixed points. -/
partial def admin (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => admin (b.instantiate1 v)
  | .mdata _ b => admin b
  | _ => e

/-- Emit a theorem tied to the original function application. All earlier
success equations and values remain in the theorem's telescope. -/
def save (owner : Name) (index : Nat) (kind : String) (params : Array Expr)
    (typ proof : Expr) : TermElabM Name := do
  let n := `R1Z.PV_RE_ComposedContext5 ++ owner ++ Name.mkSimple (kind ++ toString index)
  let ty ← mkForallFVars params typ
  let val ← mkLambdaFVars params proof
  if val.hasSorry || val.hasMVar || ty.hasMVar then throwError "incomplete context {n}"
  addDecl (Declaration.thmDecl ⟨⟨n, [], ty⟩, val, [n]⟩)
  return n

partial def spine (owner : Name) (root e outer eqRoot forward : Expr) (params : Array Expr)
    (index : Nat) : TermElabM (Array Name) := do
  let e := admin e
  if e.getAppFn.isConstOf ``Aeneas.Std.uncurry then
    let ci ← getConstInfo ``Aeneas.Std.uncurry
    let some value := ci.value? | throwError "opaque uncurry"
    let value := value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!
    let next := admin (value.beta e.getAppArgs)
    if next == e then throwError "uncurry did not advance"
    return ← spine owner root next outer eqRoot forward params index
  let args := e.getAppArgs
  if (e.getAppFn.isConstOf ``Bind.bind || e.getAppFn.isConstOf ``Aeneas.Std.bind) && args.size ≥ 2 then
    let x := args[args.size-2]!
    let k := args[args.size-1]!
    let xt ← inferType x
    let kt ← whnf (← inferType k)
    if !kt.isForall then throwError "invalid continuation"
    let α := kt.bindingDomain!
    let childOuter ← withLocalDeclD `pending xt fun r => do
      let body ← mkAppM ``Aeneas.Std.bind #[r,k]
      mkLambdaFVars #[r] (outer.beta #[body])
    let bindForward ← mkAppM ``R1Z.PV_RE_NoCatchCore.bind_noCatch #[k]
    let childForward ← mkAppM ``R1Z.PV_RE_NoCatchCore.compose #[bindForward,forward]
    let left ← spine (owner ++ Name.mkSimple ("callee" ++ toString index)) root x childOuter eqRoot childForward params 0
    let right ← withLocalDeclD (Name.mkSimple ("value" ++ toString index)) α fun v => do
      let ok ← mkAppM ``Aeneas.Std.Result.ok #[v]
      withLocalDeclD (Name.mkSimple ("prefix" ++ toString index)) (← mkEq x ok) fun h => do
        let p ← mkAppM ``R1Z.PV_RE_SourceContexts.bind_ok #[x,v,k,h]
        let p ← mkCongrArg outer p
        let p ← mkEqTrans eqRoot p
        let n ← save owner index "advance" (params ++ #[v,h]) (← inferType p) p
        let rest ← spine owner root (k.beta #[v]) outer p forward (params ++ #[v,h]) (index+1)
        return #[n] ++ rest
    return left ++ right
  else if (e.getAppFn.isConstOf ``ite || e.getAppFn.isConstOf ``dite) && args.size == 5 then
    let α := args[0]!
    let c := args[1]!
    let inst := args[2]!
    let yes := args[3]!
    let no := args[4]!
    let dep := e.getAppFn.isConstOf ``dite
    let left ← withLocalDeclD `branch_true c fun h => do
      let p ← mkAppOptM (if dep then ``dif_pos else ``if_pos)
        #[some c, some inst, some h, some α, some yes, some no]
      let p ← mkCongrArg outer p
      let p ← mkEqTrans eqRoot p
      spine (owner ++ `yes) root (if dep then yes.beta #[h] else yes) outer p forward (params.push h) index
    let right ← withLocalDeclD `branch_false (mkApp (mkConst ``Not) c) fun h => do
      let p ← mkAppOptM (if dep then ``dif_neg else ``if_neg)
        #[some c, some inst, some h, some α, some yes, some no]
      let p ← mkCongrArg outer p
      let p ← mkEqTrans eqRoot p
      spine (owner ++ `no) root (if dep then no.beta #[h] else no) outer p forward (params.push h) index
    return left ++ right
  else if let some matcher ← (do
    let m ← matchMatcherApp? e (alsoCasesOn := true)
    let env ← getEnv
    -- Inspect the discriminant type before any matcher reduction. Scalar
    -- literal matchers remain behind a separately compiled symbolic lemma.
    pure m) then
    if matcher.discrs.size != 1 then
      logInfo m!"PREFIX_CONTEXT_STOP_MULTI_MATCH {owner} after {index}"
      return #[]
    let discr := matcher.discrs[0]!
    let dt ← whnf (← inferType discr)
    let .const dn levels := dt.getAppFn | throwError "non inductive match {dt}"
    if dn == ``Aeneas.Std.UScalar then
      logInfo m!"COMPOSED_CONTEXT_SCALAR_SHAPE {owner}: use PV_RE_LiteralShape5.legacy_success separately"
      return #[]
    let .inductInfo ind ← getConstInfo dn | throwError "non inductive match {dn}"
    if ind.numIndices != 0 then
      logInfo m!"PREFIX_CONTEXT_STOP_INDEXED_MATCH {owner} after {index}"
      return #[]
    let mut names := #[]
    for ctor in ind.ctors do
      let cv := mkAppN (mkConst ctor levels) (dt.getAppArgs.extract 0 ind.numParams)
      let more ← forallTelescope (← inferType cv) fun fields _ => do
        let value := mkAppN cv fields
        withLocalDeclD `branch_constructor (← mkEq discr value) fun h => do
          let g ← withLocalDeclD `discriminant dt fun z =>
            mkLambdaFVars #[z] (e.replace fun a => if a == discr then some z else none)
          let p ← mkCongrArg g h
          let p ← mkCongrArg outer p
          let p ← mkEqTrans eqRoot p
          let selected ← withTransparency .reducible <| whnf (g.beta #[value])
          spine (owner ++ ctor) root selected outer p forward (params ++ fields ++ #[h]) index
      names := names ++ more
    return names
  else
    let n ← save owner index "context" params (← inferType eqRoot) eqRoot
    let nf ← save owner index "forward" params (← inferType forward) forward
    let et ← inferType e
    let some payload := (et.getAppArgs)[0]? | throwError "not a result leaf {e}"
    let failName ← withLocalDeclD `err (mkConst ``Aeneas.Std.Error) fun err => do
      let fail ← mkAppOptM ``Aeneas.Std.Result.fail #[some payload, some err]
      withLocalDeclD `callee_failure (← mkEq e fail) fun h => do
        let p ← mkAppM ``R1Z.PV_RE_SourceContexts.context_failure #[root,e,outer,err,eqRoot,forward,h]
        save owner index "failure" (params ++ #[err,h]) (← inferType p) p
    let div ← mkAppOptM ``Aeneas.Std.Result.div #[some payload]
    let divName ← withLocalDeclD `callee_divergence (← mkEq e div) fun h => do
      let p ← mkAppM ``R1Z.PV_RE_SourceContexts.context_divergence #[root,e,outer,eqRoot,forward,h]
      save owner index "divergence" (params.push h) (← inferType p) p
    logInfo m!"COMPOSED_CONTEXT_LEAF {owner} after {index}: {e.getAppFn}"
    return #[n,nf,failName,divName]

elab "pv_composed5_source_contexts " n:ident : command => do
  let names ← liftTermElabM do
    let ci ← getConstInfo n.getId
    let some value := ci.value? | throwError "opaque source {n.getId}"
    forallTelescope ci.type fun params _ => do
      let body := value.beta params
      if body.getAppFn.isConstOf ``Lean.Order.fix then
        logInfo m!"COMPOSED_CONTEXT_FIXED_POINT {n.getId}: requires named unrolling equation"
        return #[]
      let root := mkAppN (mkConst n.getId) params
      let eqRoot ← mkEqRefl root
      let rt ← inferType root
      let payload := rt.getAppArgs[0]!
      let identity ← withLocalDeclD `result rt fun r => mkLambdaFVars #[r] r
      let forward ← mkAppOptM ``R1Z.PV_RE_SourceContexts.identity_noCatch #[some payload]
      spine n.getId root body identity eqRoot forward params 0
  logInfo m!"PREFIX_CONTEXT_COUNT {n.getId}: {names.size}"
  for n in names do
    elabCommand (← `(command| #print axioms $(mkIdent n)))
end R1Z.PV_RE_ComposedContextsGenerator5
