import R1Z.PV_RE_NoCatchGenerator
import Lean
open Lean Meta Elab Command Term
namespace R1Z.PV_RE_SupportGenerator
/-- Reuse the checked symbolic algorithm for a NEW whole-client theorem.
No prior suffix congruence target is recompiled. -/
def theoremName (n : Name) : Name := `R1Z.PV_RE_SourceSupport ++ n

def dictionaryParam (n : Name) : MetaM Bool := do
  let c ← getConstInfo n
  match c.type with
  | .forallE _ (.const `ProverRwFull.ExternalTypes _) b _ =>
    match b with
    | .forallE _ t _ _ => return t.getAppFn.constName? == some `ProverRwFull.ExternalFuns
    | _ => return false
  | _ => return false

partial def supportFromType (t : Expr) : Array Name :=
  match t with
  | .forallE n _ b _ =>
    let rest := supportFromType b
    if n.toString.startsWith "op" then #[n] ++ rest else rest
  | _ => #[]

partial def withAgreements (ops : Array Name) (ty d1 d2 : Expr) (i : Nat)
    (hs : Array Expr) (k : Array Expr → TermElabM Expr) : TermElabM Expr := do
  if i < ops.size then
    let op := Lean.mkConst (`ProverRwFull.ExternalFuns ++ ops[i]!)
    let t ← mkEq (mkApp2 op ty d1) (mkApp2 op ty d2)
    withLocalDeclD ops[i]! t fun h => withAgreements ops ty d1 d2 (i+1) (hs.push h) k
  else k hs

/-- Structural congruence on a symbolic body. No application is evaluated. -/
partial def symbolic (e ty d1 d2 : Expr) (support : Array Name) (hs : Array Expr) : MetaM Expr := do
  if !(e.find? (· == d1)).isSome then return ← mkEqRefl e
  if ← isProof e then return ← mkEqRefl e
  if (← whnf (← inferType e)).isSort then
    if ← isDefEq e (e.replaceFVar d1 d2) then return ← mkEqRefl e
  if e.isApp && e.getAppNumArgs == 2 then
    let args := e.getAppArgs
    if args[0]! == ty && args[1]! == d1 then
      if let .const n _ := e.getAppFn then
        if n.getPrefix == `ProverRwFull.ExternalFuns then
          return hs[support.idxOf n.getString!.toName]!
        let ci ← getConstInfo (theoremName n)
        let ops := supportFromType ci.type
        return mkAppN (Lean.mkConst (theoremName n))
          (#[ty,d1,d2] ++ ops.map (fun op => hs[support.idxOf op]!))
  if e.getAppFn.isConstOf ``Lean.Order.fix then
    let args := e.getAppArgs
    let ct ← mkHCongrWithArity e.getAppFn args.size
    let mut ps := #[]
    for a in args, kind in ct.argKinds do
      let b := a.replaceFVar d1 d2
      let h ← if ← isProof a then
          if kind == .eq then mkEqRefl a else mkAppM ``proof_irrel_heq #[a,b]
        else do
          let h ← symbolic a ty d1 d2 support hs
          if kind == .eq then pure h else mkHEqOfEq h
      ps := ps ++ #[a,b,h]
    return ← mkEqOfHEq (mkAppN ct.proof ps)
  match e with
  | .app f a => return ← mkCongr (← symbolic f ty d1 d2 support hs) (← symbolic a ty d1 d2 support hs)
  | .lam n t b bi =>
    withLocalDecl n bi t fun x => do
      let h ← symbolic (b.instantiate1 x) ty d1 d2 support hs
      mkAppM ``funext #[← mkLambdaFVars #[x] h]
  | .letE _ _ v b _ => symbolic (b.instantiate1 v) ty d1 d2 support hs
  | .mdata _ b => symbolic b ty d1 d2 support hs
  | .proj n i b =>
    let bt ← inferType b
    let f := Expr.lam `x bt (.proj n i (.bvar 0)) .default
    mkCongrArg f (← symbolic b ty d1 d2 support hs)
  | _ => throwError "unhandled dictionary occurrence {e}"

/-- Each step unfolds one named function and rewrites only its immediate
callee congruences and callback equalities. Fixed points remain symbolic. -/
partial def build (n : Name) : TermElabM (Array Name) := do
  let tn := theoremName n
  if (← getEnv).contains tn then
    return supportFromType (← getConstInfo tn).type
  let ci ← getConstInfo n
  if n.getPrefix == `ProverRwFull.ExternalFuns then
    return #[n.getString! |> Name.mkSimple]
  let some value := ci.value? | throwError "opaque dictionary consumer {n}"
  let mut children : Array (Name × Array Name) := #[]
  let mut support : Array Name := #[]
  for dep in value.getUsedConstants do
    if dep != n && (← dictionaryParam dep) && !(← isProp (← getConstInfo dep).type) then
      let ops ← build dep
      children := children.push (dep, ops)
      for op in ops do
        if !support.contains op then support := support.push op
  support := support.qsort (fun a b => a.toString < b.toString)
  discard <| withLocalDeclD `types (Lean.mkConst `ProverRwFull.ExternalTypes) fun ty => do
    let dt := mkApp (Lean.mkConst `ProverRwFull.ExternalFuns) ty
    withLocalDeclD `D1 dt fun d1 => withLocalDeclD `D2 dt fun d2 => do
      withAgreements support ty d1 d2 0 #[] fun hs => do
        let lhs := mkApp2 (Lean.mkConst n) ty d1
        let rhs := mkApp2 (Lean.mkConst n) ty d2
        let goal ← mkEq lhs rhs
        -- Delta of exactly this declaration; no recursive equation unfolding.
        let lv := value.beta #[ty,d1]
        let proof ← symbolic lv ty d1 d2 support hs
        if proof.hasSorry then throwError "refusing incomplete proof {n}"
        let params := #[ty,d1,d2] ++ hs
        let typ ← mkForallFVars params goal
        let val ← mkLambdaFVars params proof
        addDecl (Declaration.thmDecl ⟨⟨tn, ci.levelParams, typ⟩, val, [tn]⟩)
        logInfo m!"DICT_CONGR {n}: {support.toList}"
        return Lean.mkConst ``True.intro
  return support

elab "pv_re3_dict_congr " n:ident : command => do
  liftTermElabM do
    discard <| build n.getId
end R1Z.PV_RE_SupportGenerator
