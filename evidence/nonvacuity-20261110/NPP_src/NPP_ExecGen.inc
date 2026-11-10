/-! EXECUTABLE ONLY: code generated from equation lemmas and definition values, NOT kernel-checked
as a proof. Nothing in this module is a theorem about the model; no proof imports it. Results
obtained through it are reported in the executable-only column (lead decision, 2026-11-10).

`NPP_X.c` is an unsafe implementation of a constant `c` that lacks compiled code on the root's
path: its body is `c`'s equation lemma (`getUnfoldEqnFor?`) when `c`'s kernel value uses a
recursor (`brecOn`, `rec`, `WellFounded.fix`), otherwise `c`'s value. In the body:
* classical decidability instances are replaced by structural instances (`NPP2.findInstTy`), and
  total-Result choices by `NPP2.okOf`/`okOkOf` (as in the kernel copies);
* every proof subterm is erased to `unsafeCast True.intro` (proofs carry no computation);
* the three id constants map to the 10 November ids; constants with a compiled `NPP_C` copy map to
  it; constants needing an implementation map to `NPP_X`.
All implementations form one mutual unsafe block (`addDecl`, falling back to unchecked addition if
the kernel rejects the block, which is logged), then `compileDecls`. -/
namespace NPP_X
open Lean Meta

def implName (n : Name) : Name := `NPP_X ++ n

def usesRecursor (v : Expr) : Bool :=
  (v.find? fun e => match e with
    | .const n _ => (match n with
        | .str _ s => s == "brecOn" || s == "binductionOn" || s == "below"
        | _ => false) || n == ``WellFounded.fix
    | _ => false).isSome

def hasCode (env : Environment) (n : Name) : Bool := (Lean.IR.findEnvDecl env n).isSome

/-- does `c` need a generated implementation -/
def needImpl (env : Environment) (idDep : NameSet) (c : Name) : MetaM Bool := do
  if NPP2.isLibConst env c then return false
  -- auxiliary recursors (casesOn, recOn, ...) and matchers are handled natively by the code generator
  if isAuxRecursor env c || isCasesOnRecursor env c || isMatcherCore env c then return false
  let some (.defnInfo d) := env.find? c | return false
  if ← isTypeFormerType d.type then return false
  if ← isProp d.type then return false
  let copy := `NPP_C ++ c
  if env.contains copy && hasCode env copy then return false
  if idDep.contains c then return true
  return !hasCode env c

def erase (P : Expr) : Expr :=
  mkApp3 (mkConst ``unsafeCast [levelZero, levelZero]) (mkConst ``True) P (mkConst ``True.intro)

/-- the refined, proof-erased body of `c` (before constant renaming) -/
def body (c : Name) : MetaM Expr := do
  let env ← getEnv
  let some (.defnInfo d) := env.find? c | throwError "not a definition {c}"
  let v ← if usesRecursor d.value then do
      match ← getUnfoldEqnFor? c (nonRec := true) with
      | some eqn =>
        let some eci := (← getEnv).find? eqn | throwError "no {eqn}"
        let ety := eci.instantiateTypeLevelParams (d.levelParams.map Level.param)
        forallTelescope ety fun xs eq => do
          let some (_, _, rhs) := eq.eq? | throwError "unexpected equation for {c}"
          mkLambdaFVars xs rhs
      | none => pure d.value
    else pure d.value
  transform v
    (pre := fun e => do
      if e.hasLooseBVars then return .continue
      if ← isProof e then return .done (erase (← instantiateMVars (← inferType e)))
      return .continue)
    (post := fun e => do
      let some k := e.getAppFn.constName? | return .done e
      if NPP2.decConsts.contains k && e.getAppNumArgs ≥ 1 then
        let cls ← inferType e
        let some inst ← NPP2.findInstTy env cls | throwError "unrefined decidability {← ppExpr e} in {c}"
        return .done inst
      if (k == ``Classical.choose || k == ``Exists.choose) && e.getAppNumArgs == 3 then
        let args := e.getAppArgs
        let some (r, shape, _) ← NPP2.okConjunct args[0]! args[1]! | throwError "unrefined choice in {c}"
        let exTy ← if shape == 1 then do
            let a ← mkFreshExprMVar args[0]!
            let _ := a
            mkAppM ``Exists #[← withLocalDeclD `a args[0]! fun a => do mkLambdaFVars #[a] (← mkEq r (← mkAppM ``Aeneas.Std.Result.ok #[a]))]
          else
            mkAppM ``Exists #[← withLocalDeclD `a args[0]! fun a => do
              mkLambdaFVars #[a] (← mkEq r (← mkAppM ``Aeneas.Std.Result.ok #[← mkAppM ``Aeneas.Std.core.result.Result.Ok #[a]]))]
        return .done (← mkAppM (if shape == 1 then ``NPP2.okOf else ``NPP2.okOkOf) #[r, erase exTy])
      return .done e)

def rename (env : Environment) (impl : NameSet) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n us =>
      if let some m := NPP2.Inputs.ids[n]? then some (.const m us)
      else if impl.contains n then some (.const (implName n) us)
      else if env.contains (`NPP_C ++ n) && hasCode env (`NPP_C ++ n) then some (.const (`NPP_C ++ n) us)
      else none
    | _ => none

/-- generate and compile the implementations reached from `root` -/
def generate (root : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let idDep := NPP2.Inputs.toSet NPP2.Inputs.idDep
  let mut impl : NameSet := {}
  let mut bodies : Array (Name × Expr) := #[]
  let mut work : Array Name := #[root]
  while h : work.size > 0 do
    let c := work.back; work := work.pop
    if impl.contains c then continue
    if !(← needImpl env idDep c) then continue
    impl := impl.insert c
    let b ← body c
    bodies := bodies.push (c, b)
    for d in b.getUsedConstants do
      if !impl.contains d then work := work.push d
  let decls : List DefinitionVal ← bodies.toList.mapM fun (c, b) => do
    let some ci := env.find? c | throwError "?"
    return { «name» := implName c, levelParams := ci.levelParams, type := rename env impl ci.type,
             value := rename env impl b, hints := .opaque, safety := .unsafe, all := bodies.toList.map (implName ·.1) }
  let names := decls.map (·.name)
  NPP2.log <| Json.mkObj [("event","exec_impls"),("count", toJson names.length),("names", toJson (names.map toString))]
  try
    addDecl (.mutualDefnDecl decls)
    NPP2.log <| Json.mkObj [("event","exec_block"),("kernel", toJson "accepted")]
  catch e =>
    NPP2.log <| Json.mkObj [("event","exec_block"),("kernel", toJson "rejected; added unchecked (executable only)"),
      ("error", toJson ((← e.toMessageData.toString).take 800).toString)]
    withOptions (fun o => debug.skipKernelTC.set o true) (addDecl (.mutualDefnDecl decls))
  compileDecls names.toArray
  return names.toArray
end NPP_X
