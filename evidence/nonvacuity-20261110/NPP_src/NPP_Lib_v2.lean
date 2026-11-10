import Lean
import Aeneas
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
universe u v

/-- computable extraction from a total Result -/
def okOf {α : Type u} : (r : Aeneas.Std.Result α) → (∃ a, r = .ok a) → α
  | .ok a, _ => a
  | .fail _, h => False.elim (h.elim fun _ e => nomatch e)
  | .div, h => False.elim (h.elim fun _ e => nomatch e)
theorem okOf_eq {α : Type u} {r : Aeneas.Std.Result α} (h : ∃ a, r = .ok a) {c : α} (e : r = .ok c) :
    okOf r h = c := by subst e; rfl
/-- computable extraction from a total `Result (core.result.Result α E)` whose value is `Ok` -/
def okOkOf {α E : Type} : (r : Aeneas.Std.Result (Aeneas.Std.core.result.Result α E)) →
    (∃ a, r = .ok (.Ok a)) → α
  | .ok (.Ok a), _ => a
  | .ok (.Err _), h => False.elim (h.elim fun _ e => nomatch e)
  | .fail _, h => False.elim (h.elim fun _ e => nomatch e)
  | .div, h => False.elim (h.elim fun _ e => nomatch e)
theorem okOkOf_eq {α E : Type} {r : Aeneas.Std.Result (Aeneas.Std.core.result.Result α E)}
    (h : ∃ a, r = .ok (.Ok a)) {c : α} (e : r = .ok (.Ok c)) : okOkOf r h = c := by subst e; rfl

/-- A proof placeholder of a choose site: `pty` (mentions the value placeholder `ph`) is its type;
`pnew` its refined proof (transported along `new = orig`), `porig` the original proof. -/
structure PSite where
  pph : FVarId
  pty : Expr
  pnew : Expr
  porig : Expr

/-- A refined site. `kind = 0`: a decidability instance (equation by `Subsingleton.elim`).
`kind = 1`: a total-Result `Classical.choose h` (`new = okOf …`, equation `eq : new = orig`), with
the proof placeholders `proofs` of every proof term whose type mentions the chosen value. -/
structure Site where
  ph : FVarId
  ty : Expr
  orig : Expr
  new : Expr
  kind : Nat := 0
  eq : Expr := .sort .zero
  key : Expr := .sort .zero
  scope : Array Expr := #[]
  newpt : Expr := .sort .zero
  eqpt : Expr := .sort .zero
  proofs : Array PSite := #[]

instance : Inhabited Site := ⟨{ ph := ⟨.anonymous⟩, ty := .sort .zero, orig := .sort .zero, new := .sort .zero }⟩

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
  -- a constant referenced by a dependent whose TYPE mentions a dependent must be copied as well
  -- (auxiliary proofs and matchers); it is placed before its first user. Fixpoint.
  for _ in [0:8] do
    let mut changed := false
    let mut newOrder : Array Name := #[]
    let mut placed : NameSet := {}
    for n in order do
      let some ci := env.find? n | continue
      if let some v := ci.value? (allowOpaque := true) then
        for c in (← usedNames [v]).toList do
          if dep.getD c false || ids.contains c || placed.contains c then continue
          let some cc := env.find? c | continue
          match cc with
          | .ctorInfo _ | .inductInfo _ | .recInfo _ | .quotInfo _ => continue
          | _ => pure ()
          if (← usedNames [cc.type]).toList.any (fun d => dep.getD d false && !ids.contains d) then
            dep := dep.insert c true; newOrder := newOrder.push c; placed := placed.insert c; changed := true
      if !placed.contains n then newOrder := newOrder.push n; placed := placed.insert n
    order := newOrder
    if !changed then break
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

/-- Recursive structural `Decidable p`: instance search; ∧/∨/¬/↔ by the core combinators;
equality with its carrier unfolded (`whnfR`, `whnf`); otherwise `p` delta-unfolded. A result
mentioning `Classical` or a noncomputable constant is rejected. The instance's type is
`Decidable p'` with `p'` definitionally equal to `p`. -/
partial def decideRec (env : Environment) (p : Expr) (fuel : Nat) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let ok (i : Expr) : MetaM (Option Expr) := do
    let i ← instantiateMVars i
    return if (badConst env i).isNone then some i else none
  if let some i ← synthInstance? (mkApp (mkConst ``Decidable) p) then
    if let some i ← ok i then return some i
  let p ← instantiateMVars p
  let bin (c : Name) (a b : Expr) : MetaM (Option Expr) := do
    let some da ← decideRec env a (fuel - 1) | return none
    let some db ← decideRec env b (fuel - 1) | return none
    ok (← mkAppOptM c #[a, b, da, db])
  if p.isAppOfArity ``And 2 then return ← bin ``instDecidableAnd p.appFn!.appArg! p.appArg!
  if p.isAppOfArity ``Or 2 then return ← bin ``instDecidableOr p.appFn!.appArg! p.appArg!
  if p.isAppOfArity ``Iff 2 then return ← bin ``instDecidableIff p.appFn!.appArg! p.appArg!
  if p.isAppOfArity ``Not 1 then
    let some da ← decideRec env p.appArg! (fuel - 1) | return none
    return ← ok (← mkAppOptM ``instDecidableNot #[p.appArg!, da])
  if let some (ty, a, b) := p.eq? then
    let u ← getLevel ty
    for ty' in [← whnfR ty, ← whnf ty] do
      if let some i ← synthInstance? (mkApp (mkConst ``Decidable) (mkApp3 (mkConst ``Eq [u]) ty' a b)) then
        if let some i ← ok i then return some i
  match ← unfoldDefinition? p with
  | some q => decideRec env (← whnfR q) (fuel - 1)
  | none =>
    let q ← whnf p
    if q != p then decideRec env q (fuel - 1) else return none

/-- As `findInst`, for an arbitrary decidability class type `cls` (`Decidable p`,
`DecidableEq α`, `DecidablePred q`, ...). -/
partial def findInstTy (env : Environment) (cls : Expr) : MetaM (Option Expr) := do
  let fn := cls.getAppFn
  let args := cls.getAppArgs
  if fn.isConstOf ``Decidable && args.size == 1 then
    return ← decideRec env args[0]! 10
  let mut cands : Array Expr := #[cls]
  for a' in [← args.mapM whnfR, ← args.mapM whnf] do
    cands := cands.push (mkAppN fn a')
  for c in cands do
    if let some i ← synthInstance? c then
      let i ← instantiateMVars i
      if (badConst env i).isNone then return some i
  return none

/-- A structural `Decidable p`: instance search at `p`, then at `p` with the equality's carrier
unfolded (`whnfR`, `whnf`), then at `p` delta-unfolded (up to three steps). The result must not
mention `Classical` or a noncomputable constant. The instance's type is `Decidable p'` with `p'`
definitionally equal to `p`. -/
def findInst (env : Environment) (p : Expr) : MetaM (Option Expr) := do
  findInstTy env (mkApp (mkConst ``Decidable) p)

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

/-- Classical decidability constants whose applications are refined as instance sites. -/
def decConsts : List Name := [``Classical.propDecidable, `Classical.decEq, `Classical.dec,
  `Classical.decPred, `Classical.decRel]

/-- For `P` (a predicate on `α`) find a conjunct `r = ok a` or `r = ok (Ok a)` of `P a`, with `r`
independent of `a`. Returns `(r, shape, proj)` where `proj : ∀ a, P a → r = K a` (`shape` 1 for
`ok`, 2 for `ok ∘ Ok`). -/
def okConjunct (α P : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
  withLocalDeclD `a α fun a => do
    let pa ← whnfR (← instantiateMVars (Expr.headBeta (mkApp P a)))
    let rec go (t : Expr) (hp : Expr) (fuel : Nat) : MetaM (Option (Expr × Nat × Expr)) := do
      match fuel with
      | 0 => return none
      | fuel+1 =>
      if t.isAppOfArity ``And 2 then
        if let some r ← go t.appFn!.appArg! (← mkAppM ``And.left #[hp]) fuel then return some r
        return ← go t.appArg! (← mkAppM ``And.right #[hp]) fuel
      if let some (_, l, rhs) := t.eq? then
        if l.containsFVar a.fvarId! then return none
        let f := rhs.getAppFn
        if f.isConst && f.constName!.getString! == "ok" && rhs.getAppNumArgs == 2 && rhs.appArg! == a then
          return some (l, 1, hp)
        if f.isConst && f.constName!.getString! == "ok" && rhs.getAppNumArgs == 2 then
          let inner := rhs.appArg!
          let g := inner.getAppFn
          if g.isConst && g.constName!.getString! == "Ok" && inner.appArg! == a then
            return some (l, 2, hp)
      return none
    withLocalDeclD `hp pa fun hp => do
      let some (l, shape, pr) ← go pa hp 8 | return none
      return some (l, shape, ← mkLambdaFVars #[a, hp] pr)

/-- nested `funext` over `xs` of a pointwise proof -/
def funextN (xs : Array Expr) (pt : Expr) : MetaM Expr := do
  let mut p := pt
  for x in xs.reverse do
    p ← mkFunExt (← mkLambdaFVars #[x] p)
  return p

/-- the first `Classical.choose`/`Exists.choose` application in `e` -/
def findChoose (e : Expr) : Option Expr :=
  e.find? fun x => (x.isAppOfArity ``Classical.choose 3 || x.isAppOfArity ``Exists.choose 3)

/-- `fun w => ∀ ys[w], ty[w]`, where `repl w x` rewrites subterms (binder types of `ys` included) -/
partial def motiveFor (ys : Array Expr) (ty : Expr) (wTy : Expr) (repl : Expr → Expr → Option Expr) :
    MetaM Expr := do
  withLocalDeclD `w wTy fun w => do
    let rec go (i : Nat) (newYs : Array Expr) : MetaM Expr := do
      if h : i < ys.size then
        let y := ys[i]
        let yty ← inferType y
        let yty' := (yty.replace (repl w)).replaceFVars (ys.extract 0 i) newYs
        withLocalDeclD `y yty' fun y' => go (i + 1) (newYs.push y')
      else
        let ty' := (ty.replace (repl w)).replaceFVars ys newYs
        mkForallFVars newYs ty'
    mkLambdaFVars #[w] (← go 0 #[])

def depPhId (n : Name) (us : List Level) : FVarId := ⟨Name.mkNum (`_npp_dep ++ n) (hash us).toNat⟩

/-- Replace every classical decidability instance, every total-Result `choose`, and every proof
whose type mentions such a `choose`, by placeholder applications; for every definition, a proof whose type mentions
exactly one copied dependency is transported along that dependency's equation. -/
def refineSites (v : Expr) (leaf : Bool := true) (isDep : Name → Bool := fun _ => false)
    (eqName : Name → Name := id) :
    MetaM (Expr × Array Site × Nat × Array ((Name × List Level) × PSite)) := do
  let sites ← IO.mkRef (#[] : Array Site)
  let depProofs ← IO.mkRef (#[] : Array ((Name × List Level) × PSite))
  let unrefined ← IO.mkRef 0
  let env ← getEnv
  let norm (x : Expr) : MetaM Expr := do
    -- Exists.choose α P h is reducible to Classical.choose α P h
    if x.isAppOfArity ``Exists.choose 3 then
      let args := x.getAppArgs
      return mkApp3 (mkConst ``Classical.choose [← getLevel args[0]!]) args[0]! args[1]! args[2]!
    return x
  -- the site index of a choose term, creating it if it has the total-Result shape
  let siteOf (c : Expr) : MetaM (Option Nat) := do
    let c ← norm c
    for i in [0:(← sites.get).size] do
      if (← sites.get)[i]!.kind == 1 && (← sites.get)[i]!.key == c then return some i
    let args := c.getAppArgs
    let (α, P, h) := (args[0]!, args[1]!, args[2]!)
    let some (r, shape, proj) ← okConjunct α P | return none
    let xs ← scopeOf c
    let h' ← mkAppM ``Exists.imp #[proj, h]
    let newv ← mkAppM (if shape == 1 then ``NPP.okOf else ``NPP.okOkOf) #[r, h']
    let spec ← mkAppM ``Classical.choose_spec #[h]
    let pe := Expr.headBeta (mkApp proj c)
    let eqpt ← mkAppM (if shape == 1 then ``NPP.okOf_eq else ``NPP.okOkOf_eq) #[h', mkApp pe spec]
    let ph ← mkFreshFVarId
    let ty ← mkForallFVars xs α
    let origL ← mkLambdaFVars xs c
    let newL ← mkLambdaFVars xs newv
    let eqf ← funextN xs eqpt
    let i := (← sites.get).size
    let site : Site := { ph, ty, orig := origL, new := newL, kind := 1, eq := eqf, key := c, scope := xs, newpt := newv, eqpt }
    sites.modify (·.push site)
    return some i
  let out ← transform v
    (pre := fun e => do
      if e.hasLooseBVars then return .continue
      if !(← isProof e) then return .continue
      let ty ← instantiateMVars (← inferType e)
      let some c := (if leaf then findChoose ty else none) | do
        -- a proof whose type mentions exactly one copied dependency: transport along its equation
        let occ ← constOccs ty isDep
        if occ.isEmpty then return .done e
        if occ.size > 1 then
          log <| Json.mkObj [("dep_proof_untransported", toJson (occ.map (·.1.toString))), ("reason", toJson "several dependencies in one proof type")]
          return .done e
        let (n, us) := occ[0]!
        let eqc := eqName n
        if !(← getEnv).contains eqc then
          log <| Json.mkObj [("dep_proof_untransported", toJson #[n.toString]), ("reason", toJson "no equation yet")]
          return .done e
        let some dci := (← getEnv).find? n | return .done e
        let α := dci.instantiateTypeLevelParams us
        let u ← getLevel α
        let eqDep := Expr.const eqc us
        let ys ← scopeOf e
        let ph := depPhId n us
        let Q ← motiveFor ys ty α fun w x => if x == .const n us then some w else none
        try Meta.check Q catch _ =>
          log <| Json.mkObj [("dep_proof_untransported", toJson #[n.toString]), ("reason", toJson "motive ill-typed")]
          return .done e
        let pnew := mkAppN (mkConst ``Eq.subst [u]) #[α, Q, .const n us, .const (`NPP_C ++ n) us,
          ← mkEqSymm eqDep, ← mkLambdaFVars ys e]
        let pph ← mkFreshFVarId
        let pty := Q.beta #[.fvar ph]
        let porig ← mkLambdaFVars ys e
        depProofs.modify (·.push ((n, us), { pph, pty, pnew, porig }))
        return .done (mkAppN (.fvar pph) ys)
      let some i ← siteOf c | do
        log <| Json.mkObj [("choose_unrefined", toJson (← ppExpr c).pretty), ("in_proof_type", toJson (← ppExpr ty).pretty)]
        unrefined.modify (· + 1); return .done e
      let st := (← sites.get)[i]!
      let c ← norm c
      let ys ← scopeOf e
      let Q ← motiveFor ys ty st.ty fun w x => if x == c then some (mkAppN w st.scope) else none
      if (findChoose (Q.beta #[.fvar st.ph])).isSome then
        log <| Json.mkObj [("choose_unrefined", toJson "proof type mentions two choices")]
        unrefined.modify (· + 1); return .done e
      let u ← getLevel st.ty
      let pnew := mkAppN (mkConst ``Eq.subst [u]) #[st.ty, Q, st.orig, st.new, ← mkEqSymm st.eq, ← mkLambdaFVars ys e]
      let pph ← mkFreshFVarId
      let pty := Q.beta #[.fvar st.ph]
      let porig ← mkLambdaFVars ys e
      let ps : PSite := { pph, pty, pnew, porig }
      sites.modify fun a => a.modify i fun st => { st with proofs := st.proofs.push ps }
      return .done (mkAppN (.fvar pph) ys))
    (post := fun e => do
      let fn := e.getAppFn
      let some c := fn.constName? | return .done e
      if leaf && decConsts.contains c && e.getAppNumArgs ≥ 1 then
        let cls ← inferType e
        let xs ← scopeOf e
        let some inst ← findInstTy env cls | do
          log <| Json.mkObj [("site_unrefined", toJson (← ppExpr e).pretty), ("class", toJson (← ppExpr cls).pretty)]
          unrefined.modify (· + 1); return .done e
        let ph ← mkFreshFVarId
        let ty ← mkForallFVars xs cls
        let origL ← mkLambdaFVars xs e
        let newL ← mkLambdaFVars xs inst
        sites.modify (·.push { ph, ty, orig := origL, new := newL })
        return .done (mkAppN (.fvar ph) xs)
      if leaf && (c == ``Classical.choose || c == ``Exists.choose) && e.getAppNumArgs == 3 then
        let some i ← siteOf e | do
          log <| Json.mkObj [("choose_unrefined", toJson (← ppExpr e.appFn!.appArg!).pretty), ("carrier", toJson (← ppExpr e.appFn!.appFn!.appArg!).pretty)]
          unrefined.modify (· + 1); return .done e
        let st := (← sites.get)[i]!
        return .done (mkAppN (.fvar st.ph) st.scope)
      return .done e)
  if leaf && (← unrefined.get) == 0 && (out.getUsedConstants.any fun c => decConsts.contains c || c == ``Classical.choose) then
    throwError "an unrefined classical constant remains"
  return (out, ← sites.get, ← unrefined.get, ← depProofs.get)

/-- One congruence step of the chain. -/
inductive Step where
  | single (lhs rhs : Expr) (pf : Option Expr)
  /-- a choose value placeholder followed by its proof placeholders -/
  | multi (vl vr e : Expr) (ph : FVarId) (T : Expr) (ptys : Array Expr) (pls prs : Array Expr)

structure Built where
  value : Expr
  F : Expr
  steps : Array Step
  nsites : Nat
  depNames : Array Name
  unrefined : Nat := 0

/-- create locals for placeholders in order (types may mention earlier placeholders) -/
partial def withPlaceholders {β : Type} (phs : List (FVarId × Expr)) (done : Array (FVarId × Expr) → MetaM β)
    (acc : Array (FVarId × Expr) := #[]) : MetaM β := do
  match phs with
  | [] => done acc
  | (f, ty) :: rest =>
    let ty' := ty.replaceFVars (acc.map (.fvar ·.1)) (acc.map (·.2))
    withLocalDeclD `_h ty' fun x => withPlaceholders rest done (acc.push (f, x))

/-- Abstract sites (if `leaf`) and dependency constants. -/
def build (ci : ConstantInfo) (leaf : Bool) (isDep : Name → Bool) (ids : Std.HashMap Name Name)
    (copyName refName eqName : Name → Name) : MetaM (Built × Bool) := do
  let env ← getEnv
  let some v := ci.value? (allowOpaque := true) | throwError "no value"
  let (v1, sites, unref, depProofs) ← refineSites v leaf isDep eqName
  let mut eqOk := true
  let body := v1.replace fun x => match x with
    | .const n us =>
      if let some m := ids[n]? then some (.const m us)
      else if isDep n then some (.fvar (depPhId n us))
      else none
    | _ => none
  let fvs := (collectFVars {} body).fvarSet
  let occ ← constOccs v1 fun n => isDep n && !ids.contains n
  let mut phs : Array (FVarId × Expr) := #[]
  let mut lhs : Array Expr := #[]
  let mut steps : Array Step := #[]
  let mut depNames : Array Name := #[]
  for st in sites do
    phs := phs.push (st.ph, st.ty); lhs := lhs.push st.new
    if st.kind == 0 then
      steps := steps.push (.single st.new st.orig none)
    else
      for ps in st.proofs do
        phs := phs.push (ps.pph, ps.pty); lhs := lhs.push ps.pnew
      steps := steps.push (.multi st.new st.orig st.eq st.ph st.ty (st.proofs.map (·.pty))
        (st.proofs.map (·.pnew)) (st.proofs.map (·.porig)))
  -- theorem dependencies whose type mentions exactly one other dependency: proof placeholders of that group
  let mut thmAttach : Array ((Name × List Level) × PSite) := #[]
  let mut attached : Array (Name × List Level) := #[]
  for (n, us) in occ do
    let some (.thmInfo tci) := env.find? n | continue
    let tdeps ← constOccs (tci.type.instantiateLevelParams tci.levelParams us) fun c => isDep c && !ids.contains c
    if tdeps.size != 1 then continue
    let (d, dus) := tdeps[0]!
    if !occ.contains (d, dus) then continue
    let tty := tci.type.instantiateLevelParams tci.levelParams us
    let pty := tty.replace fun x => if x == .const d dus then some (.fvar (depPhId d dus)) else none
    thmAttach := thmAttach.push ((d, dus), { pph := depPhId n us, pty, pnew := .const (copyName n) us, porig := .const (refName n) us })
    attached := attached.push (n, us)
  let depProofs := depProofs ++ thmAttach
  let occ := occ.filter (!attached.contains ·)
  for (n, us) in occ do
    let f : FVarId := ⟨Name.mkNum (`_npp_dep ++ n) (hash us).toNat⟩
    if !fvs.contains f then throwError "placeholder for {n} not found"
    let some dci := env.find? n | throwError "unknown {n}"
    let ty := dci.instantiateTypeLevelParams us
    phs := phs.push (f, ty); lhs := lhs.push (.const (copyName n) us)
    depNames := depNames.push n
    let dps := (depProofs.filter (·.1 == (n, us))).map (·.2)
    if !dps.isEmpty then
      for ps in dps do
        phs := phs.push (ps.pph, ps.pty); lhs := lhs.push ps.pnew
      steps := steps.push (.multi (.const (copyName n) us) (.const (refName n) us) (.const (eqName n) us) f ty
        (dps.map (·.pty)) (dps.map (·.pnew)) (dps.map (·.porig)))
      continue
    match dci with
    | .thmInfo _ =>
      match env.find? (copyName n) with
      | some cc => if cc.instantiateTypeLevelParams us == ty then
                     steps := steps.push (.single (.const (copyName n) us) (.const (refName n) us)
                       (some (mkApp2 (mkConst ``Eq.refl [Level.zero]) ty (.const (copyName n) us))))
                   else eqOk := false; steps := steps.push (.single (.const (copyName n) us) (.const (refName n) us) (some (mkConst ``True)))
      | none => eqOk := false; steps := steps.push (.single (.const (copyName n) us) (.const (refName n) us) (some (mkConst ``True)))
    | _ => steps := steps.push (.single (.const (copyName n) us) (.const (refName n) us) (some (.const (eqName n) us)))
  let F ← withPlaceholders phs.toList fun locals => do
    let body' := body.replaceFVars (locals.map (.fvar ·.1)) (locals.map (·.2))
    mkLambdaFVars (locals.map (·.2)) body'
  let value ← Core.betaReduce (F.beta lhs)
  return ({ value, F, steps, nsites := sites.size, depNames, unrefined := unref }, eqOk)

/-- the congruence chain `F lhs = F rhs` -/
def chain (b : Built) : MetaM Expr := do
  let mut h ← mkEqRefl b.F
  -- the two sides, kept as explicit (unreduced) applications of F
  let mut G1 := b.F
  let mut G2 := b.F
  for st in b.steps do
    match st with
    | .single l r pf =>
      let pf ← match pf with
        | some p => pure p
        | none => mkAppM ``Subsingleton.elim #[l, r]
      h ← mkCongr h pf
      G1 := mkApp G1 l; G2 := mkApp G2 r
    | .multi vl vr e ph T ptys pls prs =>
      -- h1 : G1 vl pls = G2 vl pls
      let mut h1 := h
      h1 ← mkCongrFun h1 vl
      for pl in pls do h1 ← mkCongrFun h1 pl
      let G2vl := mkAppN G2 (#[vl] ++ pls)
      -- h2 : G2 vl pls = G2 vr prs, by Eq.rec on e : vl = vr (proof arguments by irrelevance)
      let u ← getLevel T
      let motive ← withLocalDeclD `v' T fun v' => do
        let eqT ← mkEq vl v'
        withLocalDeclD `he eqT fun he => do
          let qtys := ptys.map fun t => t.replaceFVar (.fvar ph) v'
          let body ← withQs qtys.toList #[] fun qs => do
            mkForallFVars qs (← mkEq G2vl (mkAppN G2 (#[v'] ++ qs)))
          mkLambdaFVars #[v', he] body
      let base ← withQs (ptys.map fun t => t.replaceFVar (.fvar ph) vl).toList #[] fun qs => do
        mkLambdaFVars qs (← mkEqRefl G2vl)
      let h2 := mkAppN (mkConst ``Eq.rec [Level.zero, u]) (#[T, vl, motive, base, vr, e] ++ prs)
      h := mkAppN (mkConst ``Eq.trans [← getLevel (← inferType G2vl)])
        #[← inferType G2vl, mkAppN G1 (#[vl] ++ pls), G2vl, mkAppN G2 (#[vr] ++ prs), h1, h2]
      G1 := mkAppN G1 (#[vl] ++ pls); G2 := mkAppN G2 (#[vr] ++ prs)
  return h
where
  withQs (tys : List Expr) (acc : Array Expr) (k : Array Expr → MetaM Expr) : MetaM Expr := do
    match tys with
    | [] => k acc
    | t :: rest => withLocalDeclD `q t fun q => withQs rest (acc.push q) k

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
  let mut blocked : NameSet := {}
  for n in order do
    let some ci := env.find? n | continue
    -- a dependent of a blocked constant (an unrefined leaf) stays noncomputable and is not copied
    let ds ← depsOf ci
    if let some b := ds.toList.find? (blocked.contains ·) then
      blocked := blocked.insert n
      log <| Json.mkObj [("n", toJson n.toString),("status","blocked"),("by", toJson b.toString)]
      continue
    -- reuse a copy (and its equation) made by an earlier stage-A run
    if (← getEnv).contains (copyName n) then
      if (← getEnv).contains (eqName n) then hasEq := hasEq.insert (copyName n)
      log <| Json.mkObj [("n", toJson n.toString),("status","reused"),("eq", toJson ((← getEnv).contains (eqName n)))]
      continue
    let leaf := leaves.contains n
    match ci with
    | .defnInfo dv =>
      if dv.safety != .safe then throwError "{n}: unsafe/partial definition in the cone"
      let (b, thmOk) ← build ci leaf isDep ids copyName id eqName
      if b.unrefined > 0 then
        blocked := blocked.insert n
        log <| Json.mkObj [("n", toJson n.toString),("status","blocked (unrefined leaf)"),("unrefined_sites", toJson b.unrefined)]
        continue
      let ty := dv.type.replace fun x => match x with
        | .const c us => if let some m := ids[c]? then some (.const m us) else if isDep c then some (.const (copyName c) us) else none
        | _ => none
      let decl := Declaration.defnDecl { dv with «name» := copyName n, type := ty, value := b.value, all := [copyName n] }
      try addDecl decl
      catch e =>
        blocked := blocked.insert n
        log <| Json.mkObj [("n", toJson n.toString),("k","def"),("status","blocked (kernel rejected copy)"),("error", toJson ((← e.toMessageData.toString).take 600).toString)]
        continue
      try compileDecls #[copyName n] (logErrors := false)
      catch e => log <| Json.mkObj [("compile_failed", toJson n.toString), ("error", toJson ((← e.toMessageData.toString).take 600).toString)]
      copied := copied.push (copyName n)
      let st ← getReducibilityStatus n
      setReducibilityStatus (copyName n) st
      -- equation (references = originals), only off the id-dependent part
      let depsOk := b.depNames.all fun c => hasEq.contains (copyName c) ||
          (match env.find? c with | some (.thmInfo _) => true | _ => false)
      if !idDep.contains n && depsOk && thmOk && ty == dv.type then
        let lv := dv.levelParams.map Level.param
        let ty ← mkEq (.const (copyName n) lv) (.const n lv)
        try
          let pf ← chain b
          addDecl (.thmDecl { «name» := eqName n, levelParams := dv.levelParams, type := ty, value := pf })
          eqs := eqs.push (eqName n); hasEq := hasEq.insert (copyName n)
        catch e =>
          log <| Json.mkObj [("n", toJson n.toString),("eq_failed", toJson ((← e.toMessageData.toString).take 600).toString)]
      log <| Json.mkObj [("n", toJson n.toString),("k","def"),("sites", toJson b.nsites),
        ("deps", toJson b.depNames.size),("eq", toJson (hasEq.contains (copyName n)))]
    | .thmInfo tv =>
      let ty := tv.type.replace fun x => match x with
        | .const c us => if let some m := ids[c]? then some (.const m us) else if isDep c then some (.const (copyName c) us) else none
        | _ => none
      let tdeps ← constOccs tv.type fun c => isDep c && !ids.contains c
      let hasIds := (← usedNames [tv.type]).toList.any ids.contains
      let lv := tv.levelParams.map Level.param
      if !hasIds && !tdeps.isEmpty && tdeps.all (fun (c, _) => (hasEq.contains (copyName c))) then
        -- transport the original theorem along the equations of the dependents in its type
        let mut p : Expr := .const n lv
        let mut cur := tv.type
        for (c, us) in tdeps do
          let some dci := env.find? c | continue
          let α := dci.instantiateTypeLevelParams us
          let u ← getLevel α
          let motive ← motiveFor #[] cur α fun w x => if x == .const c us then some w else none
          p := mkAppN (mkConst ``Eq.subst [u]) #[α, motive, .const c us, .const (copyName c) us,
            ← mkEqSymm (.const (eqName c) us), p]
          cur := cur.replace fun x => if x == .const c us then some (.const (copyName c) us) else none
        try
          addDecl (.thmDecl { tv with «name» := copyName n, type := ty, value := p, all := [copyName n] })
          copied := copied.push (copyName n)
          log <| Json.mkObj [("n", toJson n.toString),("k","thm"),("by","transport"),("deps_in_type", toJson tdeps.size)]
        catch e =>
          blocked := blocked.insert n
          log <| Json.mkObj [("n", toJson n.toString),("k","thm"),("status","blocked (transport failed)"),("error", toJson ((← e.toMessageData.toString).take 600).toString)]
      else
        let (b, _) ← build ci false isDep ids copyName id eqName
        try
          addDecl (.thmDecl { tv with «name» := copyName n, type := ty, value := b.value, all := [copyName n] })
          copied := copied.push (copyName n)
          log <| Json.mkObj [("n", toJson n.toString),("k","thm"),("by","substitution"),("type_changed", toJson (ty != tv.type))]
        catch e =>
          blocked := blocked.insert n
          log <| Json.mkObj [("n", toJson n.toString),("k","thm"),("status","blocked (substitution failed)"),("error", toJson ((← e.toMessageData.toString).take 600).toString)]
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
      let missing := b.depNames.toList.map eqName |>.filter fun c => !(env.contains c) && !eqs.contains c
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
        log <| Json.mkObj [("n", toJson n.toString),("status","ok"),("deps", toJson b.depNames.size)]
      catch e =>
        failed := failed.push n
        log <| Json.mkObj [("n", toJson n.toString),("status","FAIL"),("error", toJson ((← e.toMessageData.toString).take 1500).toString)]
    | _ => pure ()
  return (eqs, failed)

end NPP
