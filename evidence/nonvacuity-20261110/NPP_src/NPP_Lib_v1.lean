import Lean
/-! NPP_ (Stream A, gate row 5, step 1). Target not yet established.

Kernel-checked computable copies ("refinements") of a definition cone, with an equation
`copy = reference` per copied definition.

* A *site* is an occurrence `@Classical.propDecidable p` inside a leaf's value. Its
  refinement is the structural instance found by `synthInstance (Decidable p)` (rejected if it
  mentions `Classical` or a noncomputable constant). With `xs` the binders `p` depends on, the
  site is abstracted as `h xs` with `h : ∀ xs, Decidable p`, and its equation is
  `Subsingleton.elim` at that Pi type (`Pi.instSubsingleton`, `instSubsingletonDecidable`).
* A *dependency* occurrence `.const y us` of a copied constant `y` is abstracted the same way;
  its equation is the already-built equation of `y`.
* With `F` the value with every site and dependency abstracted, the copy's value is `F lhs` and
  the equation is the congruence chain `F lhs = F rhs`, stated as `copy = reference`. The kernel
  checks it by delta/beta only.
Nothing here evaluates a model term. -/
open Lean Meta

namespace NPP

structure Site where
  ph : FVarId
  ty : Expr
  orig : Expr
  new : Expr

def log (j : Json) : IO Unit := do IO.println j.compress; (← IO.getStdout).flush

/-- constants of an expression, including projection structure names -/
def usedNames (es : List Expr) : MetaM NameSet := do
  let r ← IO.mkRef ({} : NameSet)
  for e in es do
    e.forEach fun x => match x with
      | .const c _ => r.modify (·.insert c)
      | .proj sn _ _ => r.modify (·.insert sn)
      | _ => pure ()
  r.get

def depsOf (ci : ConstantInfo) : MetaM NameSet :=
  match ci.value? (allowOpaque := true) with
  | some v => usedNames [ci.type, v]
  | none => usedNames [ci.type]

/-- (name, levels) occurrences of constants satisfying `p` -/
def constOccs (e : Expr) (p : Name → Bool) : MetaM (Array (Name × List Level)) := do
  let r ← IO.mkRef (#[] : Array (Name × List Level))
  e.forEach fun x => match x with
    | .const c us => do if p c && !(← r.get).contains (c, us) then r.modify (·.push (c, us))
    | _ => pure ()
  r.get

/-- Post-order walk from `root` restricted to `cand ∪ ids`; `dep n` iff `n` is a leaf, an id
target, or mentions a dependent. Returns the dependents in post-order (id targets excluded). -/
def walk (env : Environment) (root : Name) (cand leaves : NameSet) (ids : Std.HashMap Name Name) :
    MetaM (Array Name × Std.HashMap Name Bool) := do
  let mut dep : Std.HashMap Name Bool := {}
  let mut started : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array (Name × Bool) := #[(root, false)]
  while h : stack.size > 0 do
    let (n, ex) := stack.back
    stack := stack.pop
    if dep.contains n then continue
    if ids.contains n then dep := dep.insert n true; continue
    match env.find? n with
    | none => dep := dep.insert n false
    | some ci =>
      let ds := (← depsOf ci).toList.filter fun d => cand.contains d || ids.contains d
      if !ex then
        if started.contains n then continue
        started := started.insert n
        stack := stack.push (n, true)
        for d in ds do
          if !dep.contains d then stack := stack.push (d, false)
      else
        let b := leaves.contains n || ds.any (fun d => dep.getD d false)
        dep := dep.insert n b
        if b then order := order.push n
  return (order, dep)

/-- fvars that `e` depends on, closed under their types, in local-context order -/
def scopeOf (e : Expr) : MetaM (Array Expr) := do
  let lctx ← getLCtx
  let mut set : FVarIdSet := (collectFVars {} e).fvarSet
  let mut changed := true
  while changed do
    changed := false
    for f in set.toList do
      let some d := lctx.find? f | continue
      for g in (collectFVars {} d.type).fvarSet.toList do
        if !set.contains g then set := set.insert g; changed := true
  let mut out := #[]
  for d in lctx do
    if set.contains d.fvarId then
      if d.isLet then throwError "site depends on a let-bound variable {d.userName}"
      out := out.push (.fvar d.fvarId)
  return out

def badConst (env : Environment) (e : Expr) : Option Name :=
  e.getUsedConstants.find? fun c => c.getRoot == `Classical || isNoncomputable env c

/-- A structural `Decidable p`: instance search at `p`, then at `p` with the equality's carrier
unfolded (`whnfR`, `whnf`), then at `p` delta-unfolded (up to three steps). The result must not
mention `Classical` or a noncomputable constant. The instance's type is `Decidable p'` with `p'`
definitionally equal to `p`. -/
def findInst (env : Environment) (p : Expr) : MetaM (Option Expr) := do
  let mut cands : Array Expr := #[p]
  if let some (ty, a, b) := p.eq? then
    let u ← getLevel ty
    for ty' in [← whnfR ty, ← whnf ty] do
      cands := cands.push (mkApp3 (mkConst ``Eq [u]) ty' a b)
  let mut q := p
  for _ in [0:3] do
    match ← unfoldDefinition? q with
    | some q' => q ← whnfR q'; cands := cands.push q
    | none => break
  for c in cands do
    if let some i ← synthInstance? (mkApp (mkConst ``Decidable) c) then
      let i ← instantiateMVars i
      if (badConst env i).isNone then return some i
  return none

/-- Field types of a structure type (for the diagnostic of an unrefined site). -/
def fieldTypes (ty : Expr) : MetaM (Array String) := do
  let ty ← whnf ty
  let some S := ty.getAppFn.constName? | return #[]
  let env ← getEnv
  let some info := getStructureInfo? env S | return #[s!"{S}: not a structure"]
  let mut out := #[s!"structure {S}"]
  for f in info.fieldNames do
    let some pf := env.find? (S ++ f) | continue
    out := out.push s!"{f} : {← ppExpr pf.type}"
  return out

/-- Replace every `Classical.propDecidable p` in `v` by a placeholder application `h xs`. -/
def refineSites (v : Expr) : MetaM (Expr × Array Site) := do
  let sites ← IO.mkRef (#[] : Array Site)
  let unrefined ← IO.mkRef 0
  let env ← getEnv
  let out ← transform v (post := fun e => do
    if e.isAppOfArity ``Classical.propDecidable 1 then
      let p := e.appArg!
      let xs ← scopeOf e
      let inst? ← findInst env p
      let some inst := inst? | do
        let mut info : Array Json := #[]
        if let some (ty, a, _) := p.eq? then
          let tyW ← whnfR ty
          let tyD ← whnf ty
          info := #[toJson (← ppExpr ty).pretty, toJson (← ppExpr tyW).pretty, toJson (← ppExpr tyD).pretty,
            toJson (← ppExpr (← inferType a)).pretty, toJson (← fieldTypes ty)]
        log <| Json.mkObj [("site_unrefined", toJson (← ppExpr p).pretty), ("types", Json.arr info),
          ("decl_context", toJson ((← getLCtx).getFVars.size))]
        unrefined.modify (· + 1)
        return .done e
      let ph ← mkFreshFVarId
      let ty ← mkForallFVars xs (mkApp (mkConst ``Decidable) p)
      let orig ← mkLambdaFVars xs e
      let new ← mkLambdaFVars xs inst
      sites.modify (·.push { ph, ty, orig, new })
      return .done (mkAppN (.fvar ph) xs)
    else return .done e)
  if (← unrefined.get) == 0 && out.getUsedConstants.contains ``Classical.propDecidable then
    throwError "an unapplied Classical.propDecidable remains"
  return (out, ← sites.get)

structure Built where
  value : Expr          -- the copy's value (beta-reduced)
  F : Expr
  lhs : Array Expr
  rhs : Array Expr
  pfs : Array (Option Expr)   -- per argument: proof of lhs = rhs (none: site, use Subsingleton)
  nsites : Nat

/-- Abstract sites (if `leaf`) and dependency constants. `copyName y`/`refName y`/`eqName y`
give the copy, the reference and the equation name of a dependent `y`. Theorem dependents are
rejected for the equation (returned `ok := false`). -/
def build (ci : ConstantInfo) (leaf : Bool) (isDep : Name → Bool) (ids : Std.HashMap Name Name)
    (copyName refName eqName : Name → Name) : MetaM (Built × Bool) := do
  let env ← getEnv
  let some v := ci.value? (allowOpaque := true) | throwError "no value"
  let (v1, sites) ← if leaf then refineSites v else pure (v, #[])
  -- dependency placeholders, one per (name, levels)
  let deps ← IO.mkRef (#[] : Array (FVarId × Name × List Level))
  let mut eqOk := true
  let body := v1.replace fun x => match x with
    | .const n us =>
      if let some m := ids[n]? then some (.const m us)
      else if isDep n then
        -- placeholder fvar id derived deterministically from the name and levels
        some (.fvar ⟨Name.mkNum (`_npp_dep ++ n) (hash us).toNat⟩)
      else none
    | _ => none
  let fvs := (collectFVars {} body).fvarSet
  let occ ← constOccs v1 fun n => isDep n && !ids.contains n
  let mut dphs : Array (FVarId × Name × List Level) := #[]
  for (n, us) in occ do
    let f : FVarId := ⟨Name.mkNum (`_npp_dep ++ n) (hash us).toNat⟩
    if fvs.contains f then dphs := dphs.push (f, n, us)
    else throwError "placeholder for {n} not found"
  deps.set dphs
  let mut phs : Array Expr := #[]
  let mut tys : Array Expr := #[]
  let mut lhs : Array Expr := #[]
  let mut rhs : Array Expr := #[]
  let mut pfs : Array (Option Expr) := #[]
  for s in sites do
    phs := phs.push (.fvar s.ph); tys := tys.push s.ty
    lhs := lhs.push s.new; rhs := rhs.push s.orig; pfs := pfs.push none
  for (f, n, us) in dphs do
    let some dci := env.find? n | throwError "unknown {n}"
    let ty := dci.instantiateTypeLevelParams us
    phs := phs.push (.fvar f); tys := tys.push ty
    lhs := lhs.push (.const (copyName n) us); rhs := rhs.push (.const (refName n) us)
    match dci with
    | .thmInfo _ =>
      -- proof irrelevance: usable only if the copy's type is literally the original type
      match env.find? (copyName n) with
      | some cc => if cc.instantiateTypeLevelParams us == ty then pfs := pfs.push (some (mkApp2 (mkConst ``Eq.refl [Level.zero]) ty (.const (copyName n) us)))
                   else eqOk := false; pfs := pfs.push (some (mkConst ``True))
      | none => eqOk := false; pfs := pfs.push (some (mkConst ``True))
    | _ => pfs := pfs.push (some (.const (eqName n) us))
  let mut F := body.abstract phs
  for i in (List.range phs.size).reverse do
    F := .lam (Name.mkNum `_h i) tys[i]! F .default
  let value ← Core.betaReduce (F.beta lhs)
  return ({ value, F, lhs, rhs, pfs, nsites := sites.size }, eqOk)

/-- the congruence chain `F lhs = F rhs` -/
def chain (b : Built) : MetaM Expr := do
  let mut h ← mkEqRefl b.F
  for i in [0:b.lhs.size] do
    let pf ← match b.pfs[i]! with
      | some p => pure p
      | none => mkAppM ``Subsingleton.elim #[b.lhs[i]!, b.rhs[i]!]
    h ← mkCongr h pf
  return h


/-- Stage A: add the copies `pre ++ n` of the dependents of `root` (leaves refined, ids replaced),
compile the copied definitions, and add `copy = original` for every copied definition that is
not id-dependent (`idDep`) and whose dependencies all have equations. -/
def stageA (root : Name) (cand leaves : NameSet) (ids : Std.HashMap Name Name) (idDep : NameSet)
    (pre : Name) : MetaM (Array Name × Array Name) := do
  let env ← getEnv
  let (order, dep) ← walk env root cand leaves ids
  log <| Json.mkObj [("event","walk"),("dependents", toJson order.size),
    ("order", toJson (order.map toString))]
  let isDep (n : Name) := dep.getD n false && !ids.contains n
  let copyName (n : Name) := pre ++ n
  let eqName (n : Name) := (pre ++ n).str "npp_eq"
  let mut eqs : Array Name := #[]
  let mut hasEq : NameSet := {}
  let mut copied : Array Name := #[]
  for n in order do
    let some ci := env.find? n | continue
    let leaf := leaves.contains n
    match ci with
    | .defnInfo dv =>
      if dv.safety != .safe then throwError "{n}: unsafe/partial definition in the cone"
      let (b, thmOk) ← build ci leaf isDep ids copyName id eqName
      let ty := dv.type.replace fun x => match x with
        | .const c us => if let some m := ids[c]? then some (.const m us) else if isDep c then some (.const (copyName c) us) else none
        | _ => none
      let decl := Declaration.defnDecl { dv with «name» := copyName n, type := ty, value := b.value, all := [copyName n] }
      addDecl decl
      try compileDecls #[copyName n] (logErrors := false)
      catch e => log <| Json.mkObj [("compile_failed", toJson n.toString), ("error", toJson ((← e.toMessageData.toString).take 600).toString)]
      copied := copied.push (copyName n)
      let st ← getReducibilityStatus n
      setReducibilityStatus (copyName n) st
      -- equation (references = originals), only off the id-dependent part
      let depsOk := b.pfs.size == b.nsites + (b.lhs.size - b.nsites) &&
        (b.lhs.toList.drop b.nsites).all fun l => match l with
          | .const c _ => hasEq.contains c || (match env.find? c with | some (.thmInfo _) => true | _ => false)
          | _ => false
      if !idDep.contains n && depsOk && thmOk && ty == dv.type then
        let lv := dv.levelParams.map Level.param
        let ty ← mkEq (.const (copyName n) lv) (.const n lv)
        let pf ← chain b
        addDecl (.thmDecl { «name» := eqName n, levelParams := dv.levelParams, type := ty, value := pf })
        eqs := eqs.push (eqName n); hasEq := hasEq.insert (copyName n)
      log <| Json.mkObj [("n", toJson n.toString),("k","def"),("sites", toJson b.nsites),
        ("deps", toJson (b.lhs.size - b.nsites)),("eq", toJson (hasEq.contains (copyName n)))]
    | .thmInfo tv =>
      let (b, _) ← build ci false isDep ids copyName id eqName
      let ty := tv.type.replace fun x => match x with
        | .const c us => if let some m := ids[c]? then some (.const m us) else if isDep c then some (.const (copyName c) us) else none
        | _ => none
      addDecl (.thmDecl { tv with «name» := copyName n, type := ty, value := b.value, all := [copyName n] })
      copied := copied.push (copyName n)
      log <| Json.mkObj [("n", toJson n.toString),("k","thm"),("type_changed", toJson (ty != tv.type))]
    | _ => throwError "{n}: dependent of kind other than def/thm (inductive or opaque); not supported"
  return (copied, eqs)


/-- Stage B: for every id-dependent copied definition `n` (post-order), add
`(pre ++ n).nov_eq : pre ++ n = refPre ++ n`, where `refPre ++ n` is the NPO_ re-instantiated
constant. Dependencies use their `nov_eq` (id-dependent) or stage A's `npp_eq`. -/
def stageB (root : Name) (cand leaves : NameSet) (ids : Std.HashMap Name Name) (idDep : NameSet)
    (pre refPre : Name) : MetaM (Array Name × Array Name) := do
  let env ← getEnv
  let (order, dep) ← walk env root cand leaves ids
  let isDep (n : Name) := dep.getD n false && !ids.contains n
  let copyName (n : Name) := pre ++ n
  let refName (n : Name) := if idDep.contains n then refPre ++ n else n
  let eqName (n : Name) := if idDep.contains n then (pre ++ n).str "nov_eq" else (pre ++ n).str "npp_eq"
  let mut eqs : Array Name := #[]
  let mut failed : Array Name := #[]
  for n in order do
    if !idDep.contains n then continue
    let some ci := env.find? n | continue
    match ci with
    | .defnInfo dv =>
      let (b, thmOk) ← build ci (leaves.contains n) isDep ids copyName refName eqName
      let missing := (b.pfs.toList.filterMap id).filter fun p => match p with
        | .const c _ => !(env.contains c) && !eqs.contains c
        | _ => false
      if !thmOk || !missing.isEmpty then
        failed := failed.push n
        log <| Json.mkObj [("n", toJson n.toString),("status","skipped"),("missing", toJson (missing.map toString))]
        continue
      let lv := dv.levelParams.map Level.param
      let ty ← mkEq (.const (copyName n) lv) (.const (refName n) lv)
      let pf ← chain b
      try
        addDecl (.thmDecl { «name» := eqName n, levelParams := dv.levelParams, type := ty, value := pf })
        eqs := eqs.push (eqName n)
        log <| Json.mkObj [("n", toJson n.toString),("status","ok"),("deps", toJson (b.lhs.size - b.nsites))]
      catch e =>
        failed := failed.push n
        log <| Json.mkObj [("n", toJson n.toString),("status","FAIL"),("error", toJson ((← e.toMessageData.toString).take 1500).toString)]
    | _ => pure ()
  return (eqs, failed)

end NPP
