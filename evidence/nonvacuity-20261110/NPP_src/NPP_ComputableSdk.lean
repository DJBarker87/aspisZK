import Lean
import NOC_Run5bHost
import NPO_DeployedIds
set_option autoImplicit false
set_option maxHeartbeats 0
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

namespace NPP.Inputs
def cand : Array String := #["AspisR1.ARQ_BankCut.checkpoint",
  "AspisR1.ARS_Coverage.SupportedEntry",
  "AspisR1.ARS_Coverage.SupportedEntry.RuntimePersistence",
  "AspisR1.ARS_Coverage.SupportedEntry.accepted1",
  "AspisR1.ARS_Coverage.SupportedEntry.accepted2",
  "AspisR1.ARS_Coverage.SupportedEntry.actions",
  "AspisR1.ARS_Coverage.SupportedEntry.admission1",
  "AspisR1.ARS_Coverage.SupportedEntry.admission2",
  "AspisR1.ARS_Coverage.SupportedEntry.final1",
  "AspisR1.ARS_Coverage.SupportedEntry.final2",
  "AspisR1.ARS_Coverage.SupportedEntry.game",
  "AspisR1.ARS_Coverage.SupportedEntry.mk",
  "AspisR1.ARS_Coverage.SupportedEntry.p",
  "AspisR1.ARS_Coverage.SupportedEntry.post1",
  "AspisR1.ARS_Coverage.SupportedEntry.post2",
  "AspisR1.ARS_Coverage.SupportedEntry.saved",
  "AspisR1.ARS_Coverage.SupportedEntry.t",
  "AspisR1.ARS_Coverage.SupportedEntry.u",
  "AspisR1.ARS_Coverage.SupportedEntry.w1",
  "AspisR1.ARS_Coverage.SupportedEntry.w2",
  "AspisR1.ARU_CutsOrigin.selected",
  "AspisR1.ARU_Factory.deployed",
  "AspisR1.ARU_PartialAccepted.accepted",
  "AspisR1.ARU_PartialFactory.original",
  "AspisR1.ARU_Replies.accepted",
  "AspisR1.ARU_Selector.selected",
  "AspisR1.ARU_SourceResults.accepted",
  "AspisR1.ARU_Support.At",
  "AspisR1.ARU_Support.At.entry",
  "AspisR1.ARU_Support.At.firstAgrees",
  "AspisR1.ARU_Support.At.mk",
  "AspisR1.ARU_Support.At.secondAgrees",
  "AspisR1.ARV_FirstPartial.accepted",
  "AspisR1.ARW_AdmittedBudget.issued",
  "AspisR1.ARW_AdmittedQueries.admitted",
  "AspisR1.ARX_AdmittedRuntime.evaluation",
  "AspisR1.ARX_AdmittedRuntime.on_admitted",
  "AspisR1.ARX_AdmittedRuntime.outside",
  "AspisR1.ARX_AdmittedRuntime.permitted",
  "AspisR1.ARX_AdmittedRuntime.permitted_iff",
  "AspisR1.ARX_AdmittedRuntime.runtime",
  "AspisR1.ARX_SourceAlternative.accepted",
  "AspisR1.CPH_Program.not_system",
  "AspisR1.CPP_Install.configuration",
  "AspisR1.DGP_HostDigest.O1",
  "AspisR1.DGP_HostDigest.O2",
  "AspisR1.DGP_HostDigest.digestSource",
  "AspisR1.DrvC_Installation.sdk",
  "AspisR1.DrvI_Installation.sdk",
  "AspisR1.FIp_Install.configuration",
  "AspisR1.FIq_Install.configuration",
  "AspisR1.FIs_Rc7_Native.accepted",
  "AspisR1.FJp_ARCore.observations",
  "AspisR1.FJp_AccountJoin.accepted",
  "AspisR1.FJp_Domination.pointwise",
  "AspisR1.FJp_Mass.bounded",
  "AspisR1.FJp_Observations.observations",
  "AspisR1.FJp_Residual.numeric",
  "AspisR1.FJp_Ret_Rc7Native.accepted",
  "AspisR1.FJv_DFinalSource.source",
  "AspisR1.FJv_DFinalSource.source.match_1",
  "AspisR1.FJv_DNativeAccepted.accepted",
  "AspisR1.FJv_Observations.observations",
  "AspisR1.FJv_Top.deployed",
  "AspisR1.Hist_Authority.keyEq",
  "AspisR1.IDa_Deployed.deployedConfiguration",
  "AspisR1.IDa_Deployed.finish",
  "AspisR1.IDa_Deployed.seed",
  "AspisR1.NNC_ActualChoices.selected",
  "AspisR1.NNC_RecSelect.selects",
  "AspisR1.NNH8_Acceptance.a3",
  "AspisR1.NNH8_Acceptance.a4",
  "AspisR1.NNH8_Acceptance.a5",
  "AspisR1.NNH8_ChargeOf.deployed_charge_of",
  "AspisR1.NNH8_DeployedOuter",
  "AspisR1.NNH8_DeployedOuterOf",
  "AspisR1.NNH8_Exec.ERec",
  "AspisR1.NNH8_Exec.clockFree",
  "AspisR1.NNH8_Exec.exec",
  "AspisR1.NNH8_Exec.exec._proof_1",
  "AspisR1.NNH8_Exec.exec._proof_2",
  "AspisR1.NNH8_Exec.exec._proof_3",
  "AspisR1.NNH8_Exec.recSelect",
  "AspisR1.NNH8_Exec.recSig",
  "AspisR1.NNH8_FirstWriter.oracle",
  "AspisR1.NNH8_FirstWriter.owned",
  "AspisR1.NNH8_FirstWriter.writer",
  "AspisR1.NNH8_FullSpace.same_event",
  "AspisR1.NNH8_Headline.headline",
  "AspisR1.NNH8_HeadlineB.headlineB",
  "AspisR1.NNH8_HeadlineB.headlineB._proof_1",
  "AspisR1.NNH8_HeadlineB.outcomeRec",
  "AspisR1.NNH8_HostCharge.bound",
  "AspisR1.NNH8_HostCharge.event_fixed",
  "AspisR1.NNH8_NMF.Associated",
  "AspisR1.NNH8_NMF.S",
  "AspisR1.NNH8_NMF.eventImage",
  "AspisR1.NNH8_NMF.nmfB",
  "AspisR1.NNH8_NMF.recSig",
  "AspisR1.NNH8_NMF.rootImage",
  "AspisR1.NNH8_NMF.selected",
  "AspisR1.NNH8_NMF.selected.match_1",
  "AspisR1.NNH8_NativeCuts.Packet",
  "AspisR1.NNH8_NativeCuts.Packet.cuts",
  "AspisR1.NNH8_NativeCuts.Packet.domain",
  "AspisR1.NNH8_NativeCuts.Packet.events",
  "AspisR1.NNH8_NativeCuts.Packet.f",
  "AspisR1.NNH8_NativeCuts.Packet.mk",
  "AspisR1.NNH8_NativeCuts.Packet.native",
  "AspisR1.NNH8_NativeCuts.Packet.origin",
  "AspisR1.NNH8_NativeCuts.Packet.persisted",
  "AspisR1.NNH8_NativeCuts.Packet.records",
  "AspisR1.NNH8_NativeCuts.Packet.s",
  "AspisR1.NNH8_NativeCuts.Packet.writerHeader",
  "AspisR1.NNH8_NativeCuts.Packet.writerRoot",
  "AspisR1.NNH8_NativeCuts.produce",
  "AspisR1.NNH8_Numeric.host_bound",
  "AspisR1.NNH8_Outer.inclusion",
  "AspisR1.NNH8_Packet.Cut",
  "AspisR1.NNH8_Packet.cuts",
  "AspisR1.NNH8_Packet.packet",
  "AspisR1.NNH8_Packet.packet._proof_1",
  "AspisR1.NNH8_Packet.packet._proof_2",
  "AspisR1.NNH8_Packet.packet._proof_3",
  "AspisR1.NNH8_Packet.packet._proof_4",
  "AspisR1.NNH8_Packet.packet._proof_5",
  "AspisR1.NNH8_Packet.packet._proof_6",
  "AspisR1.NNH8_Packet.packet._proof_7",
  "AspisR1.NNH8_Packet.packet._proof_8",
  "AspisR1.NNH8_Packet.select",
  "AspisR1.NNH8_Packet.source",
  "AspisR1.NNH8_Persistence.key",
  "AspisR1.NNH8_Persistence.persisted",
  "AspisR1.NNH8_Physical.deployed_splitB_of",
  "AspisR1.NNH8_Producers.accepted",
  "AspisR1.NNH8_Producers.game",
  "AspisR1.NNH8_Producers.origin",
  "AspisR1.NNH8_Producers.produce",
  "AspisR1.NNH8_ProtCells.produce",
  "AspisR1.NNH8_ProtLamports.produce",
  "AspisR1.NNH8_ProtMarker.produce",
  "AspisR1.NNH8_ProtOwner.produce",
  "AspisR1.NNH8_ProtPositive.produce",
  "AspisR1.NNH8_ProtPreserves.produce",
  "AspisR1.NNH8_Protection.produce",
  "AspisR1.NNH8_RecorderFixed.base",
  "AspisR1.NNH8_RecorderFixed.fixed",
  "AspisR1.NNH8_RecorderFixed.fixedProgram",
  "AspisR1.NNH8_RecorderFixed.program",
  "AspisR1.NNH8_Rest.Delivered",
  "AspisR1.NNH8_Rest.assemble",
  "AspisR1.NNH8_RestClaims.Goal",
  "AspisR1.NNH8_RestClaims.produce",
  "AspisR1.NNH8_RestCopy.CopyFacts",
  "AspisR1.NNH8_RestCopy.produce",
  "AspisR1.NNH8_RestEvents.produce",
  "AspisR1.NNH8_RestInstallation.produce",
  "AspisR1.NNH8_RestRecorder.produce",
  "AspisR1.NNH8_RestSetup.Goal",
  "AspisR1.NNH8_RestSetup.produce",
  "AspisR1.NNH8_RestTrace.produce",
  "AspisR1.NNH8_Retime.first",
  "AspisR1.NNH8_Retime.missing",
  "AspisR1.NNH8_Retime.sdk_same",
  "AspisR1.NNH8_Retime.second",
  "AspisR1.NNH8_Split.conclusion_iff",
  "AspisR1.NNH8_Split.outcome",
  "AspisR1.NNH8_Split.rest",
  "AspisR1.NNH8_Top.deployed_splitB_of",
  "AspisR1.NNH8_TopHost.R",
  "AspisR1.NNH8_TopHost.RestLaw",
  "AspisR1.NNH8_TopHost.S",
  "AspisR1.NNH8_TopHost.X",
  "AspisR1.NNH8_TopHost.g1a",
  "AspisR1.NNH8_TopHost.nmfB",
  "AspisR1.NNH8_TopHost.split",
  "AspisR1.NNH8_Weak241.inputs",
  "AspisR1.NNH_DigestSyntaxTransport.o1",
  "AspisR1.NNH_HostCtx.base",
  "AspisR1.NNH_HostCtx.configuration",
  "AspisR1.NNH_HostCtx.missing",
  "AspisR1.NNH_HostCtx.missingLit",
  "AspisR1.NNH_HostCtx.sdk",
  "AspisR1.NNH_HostWeak241.reference",
  "AspisR1.NNH_OutcomeRecAccepted.accepted",
  "AspisR1.NNH_RecordedCharge.bound",
  "AspisR1.NNH_RecordedCharge.recorder",
  "AspisR1.NNH_RecordedCharge.source",
  "AspisR1.NNH_ResultPortTransport.finish",
  "AspisR1.NNH_Run5bCtx.configuration",
  "AspisR1.NNH_Run5bCtx.sdk",
  "AspisR1.NNH_Run5bCurrentExpand.semantic",
  "AspisR1.NNH_Run5bCurrentExpand.semantic_slot",
  "AspisR1.NNH_Run5bCurrentInitial.returned",
  "AspisR1.NNH_Run5bCurrentInitial.slot",
  "AspisR1.NNH_Run5bCurrentInventory.adapter",
  "AspisR1.NNH_Run5bCurrentPending.source",
  "AspisR1.NNH_Run5bCurrentShape.current",
  "AspisR1.NNH_Run5bCurrentShape.parse",
  "AspisR1.NNH_Run5bCurrentShape.slot",
  "AspisR1.NNH_Run5bCurrentView.returned",
  "AspisR1.NNH_Run5bCurrentView.slot",
  "AspisR1.NNH_Run5bFinishEdge.selected",
  "AspisR1.NNH_Run5bGeometryMap.source",
  "AspisR1.NNH_Run5bGeometryReverse.selected",
  "AspisR1.NNH_Run5bGeometrySlots.double",
  "AspisR1.NNH_Run5bGeometrySlots.inverse",
  "AspisR1.NNH_Run5bGeometrySlots.line",
  "AspisR1.NNH_Run5bGeometrySlots.multiply",
  "AspisR1.NNH_Run5bGeometrySlots.one",
  "AspisR1.NNH_Run5bGeometrySlots.ops",
  "AspisR1.NNH_Run5bGeometrySlots.point",
  "AspisR1.NNH_Run5bGeometrySlots.subtract",
  "AspisR1.NNH_Run5bPreparedModel.source",
  "AspisR1.NNH_Run5bPreparedSlot.fixed",
  "AspisR1.NNH_Run5bQuerySlots.actual",
  "AspisR1.NNH_Run5bQuerySlots.circle",
  "AspisR1.NNH_Run5bQuerySlots.decode",
  "AspisR1.NNH_Run5bQuerySlots.dots",
  "AspisR1.NNH_Run5bQuerySlots.geometry",
  "AspisR1.NNH_Run5bQuerySlots.line",
  "AspisR1.NNH_Run6Fields.I",
  "AspisR1.NNH_Run6Fields.children",
  "AspisR1.NNH_Run6Fields.install",
  "AspisR1.NNH_Run6Fields.nmm",
  "AspisR1.NNH_Run6Fields.nmo",
  "AspisR1.NNH_Run6Fields.nmp",
  "AspisR1.NNH_Run6Fields.nms",
  "AspisR1.NNH_Run6Fields.nmt",
  "AspisR1.NNH_Run6Fields.nmv",
  "AspisR1.NNH_Run6Fields.nmw",
  "AspisR1.NNH_Run6Fields.nmx",
  "AspisR1.NNH_Run6Installed.implementation",
  "AspisR1.NNH_Run6ReaderNative.native",
  "AspisR1.NNH_StateSelect.selects",
  "AspisR1.NNH_Tx2LiteralSlots.constants",
  "AspisR1.NNH_Tx2LiteralSlots.pending",
  "AspisR1.NNH_Tx2LiteralSlots.powers",
  "AspisR1.NNH_Tx2SlotTransport.finish_slot",
  "AspisR1.NNH_Tx2SlotTransport.geometry_slot",
  "AspisR1.NNH_Tx2SlotTransport.stage",
  "AspisR1.NNH_Weak241Prefix.Packet",
  "AspisR1.NNH_Weak241Prefix.Packet.encode_ok",
  "AspisR1.NNH_Weak241Prefix.Packet.mk",
  "AspisR1.NNH_Weak241Prefix.Packet.n_eq",
  "AspisR1.NNH_Weak241Prefix.Packet.reads",
  "AspisR1.NNH_Weak241Prefix.Packet.validate_ok",
  "AspisR1.NNH_Weak241Prefix.Packet.validated",
  "AspisR1.NNH_Weak241Prefix.produce",
  "AspisR1.NNH_WeakReaderCuts.produce",
  "AspisR1.NNH_WeakTx2Inputs.Packet",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpoint",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpointAccount",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpoint_eq",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpoint_index",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpoint_read",
  "AspisR1.NNH_WeakTx2Inputs.Packet.encode",
  "AspisR1.NNH_WeakTx2Inputs.Packet.encoded",
  "AspisR1.NNH_WeakTx2Inputs.Packet.extent",
  "AspisR1.NNH_WeakTx2Inputs.Packet.logical",
  "AspisR1.NNH_WeakTx2Inputs.Packet.mk",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proof",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proofAccount",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proof_eq",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proof_index",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proof_read",
  "AspisR1.NNH_WeakTx2Inputs.Packet.public_eq",
  "AspisR1.NNH_WeakTx2Inputs.Packet.validate",
  "AspisR1.NNH_WeakTx2Inputs.Packet.validated",
  "AspisR1.NNH_WeakTx2Inputs.produce",
  "AspisR1.NNQ_HostDigest.o2",
  "AspisR1.NNQ_HostDigest.split",
  "AspisR1.NNR_ClockFree.modelSlots",
  "AspisR1.NNU_Geometry.source",
  "AspisR1.NNU_GeometrySelected.gather",
  "AspisR1.NNU_GeometrySelected.prefixCall",
  "AspisR1.NNU_GeometrySelected.zero",
  "AspisR1.NNU_GeometryTraversal.selected_loop",
  "AspisR1.NNU_GeometryTraversal.selected_step",
  "AspisR1.NNU_MerkleSlots.installed",
  "AspisR1.NNU_Query.source",
  "AspisR1.NNU_QueryAccum.power",
  "AspisR1.NNU_QueryAccum.product",
  "AspisR1.NNU_QueryAccum.slots",
  "AspisR1.NNU_QueryAccum.source",
  "AspisR1.NNU_QueryAccum.sum",
  "AspisR1.NNU_QueryLoop.finite",
  "AspisR1.NNU_QueryLoop.source",
  "AspisR1.NNU_QueryValues.source",
  "AspisR1.NNU_Stage2Tail.emitPacket",
  "AspisR1.NNU_Stage2Tail.returnedCuts",
  "AspisR1.NNV_AdapterEncodeHost.slot",
  "AspisR1.NNV_CheckpointDigest.source",
  "AspisR1.NNV_CurrentCheckpoint.slot",
  "AspisR1.NNV_CurrentCheckpoint.source",
  "AspisR1.NNV_CurrentFlush.returned",
  "AspisR1.NNV_CurrentFlush.slot",
  "AspisR1.NNV_CurrentGeometry.returned",
  "AspisR1.NNV_CurrentGeometry.slot",
  "AspisR1.NNV_CurrentGeometry.source",
  "AspisR1.NNV_CurrentQuerySource.slot",
  "AspisR1.NNV_CurrentQuerySource.source",
  "AspisR1.NNV_CurrentScan.returned",
  "AspisR1.NNV_CurrentScan.slot",
  "AspisR1.NNV_CurrentScan.source",
  "AspisR1.NNV_GeometryBody.source",
  "AspisR1.NNV_GeometryEq.source",
  "AspisR1.NNV_GeometryIndexPorts.first",
  "AspisR1.NNV_GeometryOuter.loop",
  "AspisR1.NNV_GeometryOuter.source",
  "AspisR1.NNV_GeometryOuter.stage",
  "AspisR1.NNV_GeometryPrefixSelected.source",
  "AspisR1.NNV_GeometryQuery.fibre",
  "AspisR1.NNV_GeometryQuery.source",
  "AspisR1.NNV_GeometrySelectedStd.any",
  "AspisR1.NNV_GeometrySelectedStd.array",
  "AspisR1.NNV_GeometrySelectedStd.base",
  "AspisR1.NNV_GeometrySelectedStd.empty",
  "AspisR1.NNV_GeometrySelectedStd.iterator",
  "AspisR1.NNV_GeometrySelectedStd.mapped",
  "AspisR1.NNV_GeometrySelectedStd.zero",
  "AspisR1.NNV_GeometryTerminal.source",
  "AspisR1.NNV_PrepareView.returned",
  "AspisR1.NNV_PreparedAtHost.digest",
  "AspisR1.NNV_PreparedAtHost.source",
  "AspisR1.NNX_CommonEncode.source",
  "AspisR1.NNX_CurrentQuery.actual",
  "AspisR1.NNX_CurrentQuery.slots",
  "AspisR1.NNX_CurrentQuery.source",
  "AspisR1.NNX_Flush.source",
  "AspisR1.NNX_LeafAgreement.source",
  "AspisR1.NNX_PreparedValue.source",
  "AspisR1.NNY_NNUParent.parent",
  "AspisR1.NNY_ParserAssociation.source",
  "AspisR1.NNY_Stage2PacketResidual.returned",
  "AspisR1.NOC_Conv094.accNew",
  "AspisR1.NOC_Conv094.geometry",
  "AspisR1.NOC_Conv094.scan",
  "AspisR1.NOC_Conv094.weightsNew",
  "AspisR1.NOC_ConvLeaves.cur",
  "AspisR1.NOC_ConvLeaves.filled",
  "AspisR1.NOC_ConvLeaves.parse",
  "AspisR1.NOC_ConvLeaves.prepared",
  "AspisR1.NOC_ConvLeaves.view",
  "AspisR1.NOC_HostCtx.Exhibited",
  "AspisR1.NOC_HostCtx.base",
  "AspisR1.NOC_HostCtx.configuration",
  "AspisR1.NOC_HostCtx.extraction",
  "AspisR1.NOC_HostCtx.missing",
  "AspisR1.NOC_HostCtx.missingLit",
  "AspisR1.NOC_HostCtx.model1",
  "AspisR1.NOC_HostCtx.model2",
  "AspisR1.NOC_HostCtx.sdk",
  "AspisR1.NOC_MerkleBounded.host",
  "AspisR1.NOC_MerkleBounded.hostNode",
  "AspisR1.NOC_MerkleBounded.hostParent",
  "AspisR1.NOC_Op9.op9",
  "AspisR1.NOC_Op9Slot.digest",
  "AspisR1.NOC_Op9Slot.slot",
  "AspisR1.NOC_PrepareConv.cur",
  "AspisR1.NOC_PrepareConv.prepare",
  "AspisR1.NOC_PrepareFront.cur",
  "AspisR1.NOC_PrepareFront.filled",
  "AspisR1.NOC_PrepareFront.logical_semantic",
  "AspisR1.NOC_PrepareFront.off_inactive",
  "AspisR1.NOC_PrepareFront.off_semantic",
  "AspisR1.NOC_PrepareFront.off_y1",
  "AspisR1.NOC_PrepareFront.source",
  "AspisR1.NOC_QueryLink.current",
  "AspisR1.NOC_Run5bClaims.conclusion",
  "AspisR1.NOC_Run5bCtx.Exhibited",
  "AspisR1.NOC_Run5bCtx.base",
  "AspisR1.NOC_Run5bCtx.configuration",
  "AspisR1.NOC_Run5bCtx.extraction",
  "AspisR1.NOC_Run5bCtx.missing",
  "AspisR1.NOC_Run5bCtx.model1",
  "AspisR1.NOC_Run5bCtx.model2",
  "AspisR1.NOC_Run5bCtx.sdk",
  "AspisR1.NOC_Run5bHost.S_host",
  "AspisR1.NOC_Run5bHost.S_host._proof_1",
  "AspisR1.NOC_Run5bHost.a0",
  "AspisR1.NOC_Run5bHost.bound",
  "AspisR1.NOC_Run5bHost.data",
  "AspisR1.NOC_Run5bHost.envSig",
  "AspisR1.NOC_Run5bHost.event",
  "AspisR1.NOC_Run5bHost.r0",
  "AspisR1.NOC_Run5bHost.record",
  "AspisR1.NOC_Run5bHost.runtime",
  "AspisR1.NOC_Run5bHost.seed",
  "AspisR1.NOC_SeedTransfer.newCfg",
  "AspisR1.NOC_SeedTransfer.op9",
  "AspisR1.NOC_SemConv.op9",
  "AspisR1.NOC_Stage1Iff.clockFree",
  "AspisR1.NOC_Stage1Iff.iff345",
  "AspisR1.NOC_Stage1Iff.sameSdk",
  "AspisR1.NOC_Stage1Iff.sdk_at_slot",
  "AspisR1.NOC_Tx1Conv.batch",
  "AspisR1.NOC_Tx1Conv.cur",
  "AspisR1.NOC_Tx1Conv.query",
  "AspisR1.NOC_Tx1Conv.tx1",
  "AspisR1.NOC_Tx1Forward.batch",
  "AspisR1.NOC_Tx1Forward.cur",
  "AspisR1.NOC_Tx1Forward.off_folded",
  "AspisR1.NOC_Tx1Forward.off_round1",
  "AspisR1.NOC_Tx1Forward.query",
  "AspisR1.NOC_Tx1Forward.source",
  "AspisR1.NOC_Tx1Forward.zero",
  "AspisR1.NOF_A2FieldCorrected.clockFree",
  "AspisR1.NOF_A2FieldCorrected.field",
  "AspisR1.NOF_A2FieldCorrected.sdk_at_slot",
  "AspisR1.NOF_CommonConverse.common",
  "AspisR1.NOF_CommonConverse.source",
  "AspisR1.NOF_CommonConverse.source_run",
  "AspisR1.NOF_CommonConverse.tail_transport",
  "AspisR1.NOF_Tx2Op11.tx2Op11",
  "AspisR1.NOM_MerkleParent.hostParent",
  "AspisR1.NOQ_A1Assembly.IFF",
  "AspisR1.NOQ_A1Assembly.errT",
  "AspisR1.NOQ_A1Assembly.field_of",
  "AspisR1.NOQ_A1Assembly.okT",
  "AspisR1.NOQ_FinalCombined.field",
  "AspisR1.NOQ_WeakErrHost.modelRet1",
  "AspisR1.Op5T_Concrete.current",
  "AspisR1.Op5T_Concrete.stage",
  "AspisR1.Op5T_Install.body",
  "AspisR1.Op5T_Install.current",
  "AspisR1.Op5T_Install.currentBatch",
  "AspisR1.Op5T_Install.stage",
  "AspisR1.Op5T_Install.stageBatch",
  "AspisR1.Port3_BatchStd.install",
  "AspisR1.Port3_BatchStd.sameLeaf",
  "AspisR1.Port3_FinishStage.ne",
  "AspisR1.Port3_FinishStage.release",
  "AspisR1.Port4B_CountInstall.nodeCount",
  "AspisR1.Port4B_Install.leaves",
  "AspisR1.Port4D_FinishInstall.finish",
  "AspisR1.Port4D_Round.native",
  "AspisR1.RPx_Deployed.deployed",
  "AspisR1.Rc5_Install.configuration",
  "AspisR1.Rc5_Install.seed",
  "AspisR1.TAS_FinalB.deployed_charge",
  "AspisR1.TAS_FinalB.deployed_splitB",
  "AspisR1.TAS_FinalB.fail_sub_rec",
  "AspisR1.Tx2I_Install.install",
  "AspisR1.Tx2I_Install.stage",
  "AspisR1.Uni_Install.current",
  "LIBB_PoolLib.deployed",
  "LIB_Deployed.deployed",
  "LIB_Deployed.ids",
  "LIB_Instances.D",
  "NGL_CheckpointModel.install",
  "NHJ_IdPacket.pool",
  "NHJ_IdPacket.registry",
  "NHY_PolicyModel.policy",
  "NJI_MasterModel.model",
  "NJI_MasterModel.terminal",
  "NJI_PolicyParser.body",
  "NJI_PolicyPort.validator",
  "NJI_V1Models.Z",
  "NJI_V1Models.entry",
  "NJI_V1Models.registry",
  "NJQ_Canonical.checkpoint",
  "NJQ_Canonical.entry",
  "NJQ_Canonical.master",
  "NJQ_Canonical.registry",
  "NJQ_Checkpoint.model",
  "NJQ_Entry.model",
  "NJQ_Master.model",
  "NJQ_Registry.model",
  "NKF_CheckpointBox.reference",
  "NKF_MasterBox.reference",
  "NMS_R2AfterAuth242.factor",
  "NMS_R2AfterAuthEq242.factor",
  "NMS_R2Gated242.source",
  "NMS_R2N_Native242Children.children",
  "NMS_R2N_Native242Children.meaning",
  "NMS_R2RequestBindings.pool",
  "NMS_R2RequestGuards.actual",
  "NMS_R2RequestGuards.bad",
  "NMS_R2RequestGuards.full",
  "NMS_R2RequestGuards.source",
  "NMX_R3_Instantiated233.native",
  "NMX_R3_Instantiated233.registry_packet",
  "NMX_R3_Instantiated233.represented",
  "NMX_R3_RegistryRoot.authenticate",
  "NMX_R3_RegistryRoot.root",
  "NMX_R4_AllArgs.execution",
  "NMX_R4_AllArgs.operational",
  "NMX_R4_Authentication.authenticate",
  "NMX_R4_Authentication.context",
  "NMX_R4_Authentication.observed",
  "NMX_R4_Authentication.root",
  "NMX_R4_NMS233.packet",
  "NMX_R4_NMS233.typed",
  "NMX_R4_NMS242Instantiation.fold",
  "NMX_R5_AfterAuth242.full",
  "NMX_R5_Decode242.full",
  "NMX_R5_Decode242.model",
  "NMX_R5_Decode242.source",
  "NMX_R5_Guards242.factor",
  "NMX_R5_Guards242.full",
  "NMX_R5_Guards242.model",
  "NMX_R5_Native242.full",
  "NMX_R5_PrefixSource242.body",
  "NMX_R5_PrefixSource242.full",
  "NMX_R5_Request242.D",
  "NMX_R5_Request242.bad",
  "NMX_R5_Request242.full",
  "NMX_R5_Request242.model",
  "NMX_R5_Slot242.D",
  "NMX_R5_Slot242.full",
  "NMX_R5_Slot242.model",
  "NMX_R5_Slot242.source",
  "NMX_R6_NativeLive242.live",
  "NMX_R6_NativeLive242.observation",
  "NMX_R6_NativeLive242.source_member",
  "NMX_R6_Nonempty.auth",
  "NMX_R6_Port242.D",
  "NMX_R6_Port242.replay_member",
  "NMX_R6_Port242.validate",
  "NMX_R6_Validation.root",
  "NMX_R6_Validation.validate",
  "NMX_R7_Port241.stage2",
  "NMX_R7_PortLaw241.replay_member",
  "NMX_R8_After241.full",
  "NMX_R8_AfterFactor241.factor",
  "NMX_R8_AfterFactor241.source",
  "NMX_R8_Children241.grouped",
  "NMX_R8_Children241.original",
  "NMX_R8_Children241.validate",
  "NMX_R8_Encoded241.full",
  "NMX_R8_EncodedFactor241.factor",
  "NMX_R8_GroupEncode241.source",
  "NMX_R8_GroupReads241.source",
  "NMX_R8_GroupValidate241.source",
  "NMX_R8_Reads241.full",
  "NMX_R8_ReadsFactor241.factor",
  "NMX_R8_ReadsFactor241.source",
  "NMX_R9_After241.fixed",
  "NMX_R9_After241.full",
  "NMX_R9_After241.grouped",
  "NMX_R9_Children241.grouped",
  "NMX_R9_Children241.original",
  "NMX_R9_Children241.validate",
  "NMX_R9_Children241.validate_full",
  "NMX_R9_GroupHead241.source",
  "NMX_R9_Head241.full",
  "NMX_R9_HeaderFactor241.factor",
  "NMX_R9_HeaderFactor241.later",
  "NMX_R9_HeaderFactor241.source",
  "NMX_R9_Live241.grouped",
  "NMX_R9_Live241.live",
  "NMX_R9_Live241.observation",
  "NMX_R9_Live241.source_member",
  "NMX_R9_Live241.validate",
  "NMX_R9_Native241.meaning",
  "NMX_R9_RelReplay241.D",
  "NMX_R9_RelReplay241.replay",
  "NMX_R9_StageTwo.D",
  "NMX_R9_StageTwo.stage2",
  "NMX_R9_ValidateUse241.full",
  "NMX_R9_ValidateUse241.source",
  "NND_DecoderSlots.install",
  "NNH_AuthCheckpointInputs.Packet",
  "NNH_AuthCheckpointInputs.Packet.checkpoint",
  "NNH_AuthCheckpointInputs.Packet.data",
  "NNH_AuthCheckpointInputs.Packet.decode",
  "NNH_AuthCheckpointInputs.Packet.domain_eq",
  "NNH_AuthCheckpointInputs.Packet.mk",
  "NNH_AuthCheckpointInputs.Packet.next",
  "NNH_AuthCheckpointInputs.Packet.pda",
  "NNH_AuthCheckpointInputs.Packet.pool_eq",
  "NNH_AuthCheckpointInputs.Packet.read",
  "NNH_AuthCheckpointInputs.produce",
  "NNH_AuthCheckpointPort.value",
  "NNH_AuthCheckpointStep.source",
  "NNH_AuthGuardPorts.data",
  "NNH_AuthGuardPorts.readonly",
  "NNH_AuthLaneInputs.Packet",
  "NNH_AuthLaneInputs.Packet.data",
  "NNH_AuthLaneInputs.Packet.decode",
  "NNH_AuthLaneInputs.Packet.lane_eq",
  "NNH_AuthLaneInputs.Packet.mk",
  "NNH_AuthLaneInputs.Packet.output",
  "NNH_AuthLaneInputs.Packet.pda",
  "NNH_AuthLaneInputs.Packet.pool_eq",
  "NNH_AuthLaneInputs.Packet.read",
  "NNH_AuthLaneInputs.Packet.state",
  "NNH_AuthLaneInputs.produce",
  "NNH_AuthLanePort.value",
  "NNH_AuthLaneStep.source",
  "NNH_AuthMasterInputs.Packet",
  "NNH_AuthMasterInputs.Packet.data",
  "NNH_AuthMasterInputs.Packet.decode",
  "NNH_AuthMasterInputs.Packet.mask_eq",
  "NNH_AuthMasterInputs.Packet.master",
  "NNH_AuthMasterInputs.Packet.mk",
  "NNH_AuthMasterInputs.Packet.next",
  "NNH_AuthMasterInputs.Packet.pda",
  "NNH_AuthMasterInputs.Packet.pool_eq",
  "NNH_AuthMasterInputs.Packet.read",
  "NNH_AuthMasterInputs.Packet.registry",
  "NNH_AuthMasterInputs.produce",
  "NNH_AuthMasterPort.value",
  "NNH_AuthMasterStep.source",
  "NNH_AuthNativeGuards.produce",
  "NNH_AuthSdkBodyPort.value",
  "NNH_AuthSdkDistinct.value",
  "NNH_AuthSdkGuards.produce",
  "NNH_AuthSdkPort.value",
  "NNH_AuthSdkTail.checkpoint",
  "NNH_AuthSdkTail.lane",
  "NNH_AuthSdkTail.master",
  "NNH_AuthSdkTail.registry",
  "NNH_AuthSlotFacts.ne_self",
  "NNH_CorrectCallInputs.produce",
  "NNH_CorrectConfiguration.configuration",
  "NNH_CorrectConfiguration.sdk",
  "NNH_CorrectExtents.value",
  "NNH_CorrectReads.source",
  "NNH_CorrectTx2Inputs.Packet",
  "NNH_CorrectTx2Inputs.Packet.checkpoint",
  "NNH_CorrectTx2Inputs.Packet.checkpointAccount",
  "NNH_CorrectTx2Inputs.Packet.checkpoint_eq",
  "NNH_CorrectTx2Inputs.Packet.checkpoint_index",
  "NNH_CorrectTx2Inputs.Packet.checkpoint_read",
  "NNH_CorrectTx2Inputs.Packet.encode",
  "NNH_CorrectTx2Inputs.Packet.encoded",
  "NNH_CorrectTx2Inputs.Packet.extent",
  "NNH_CorrectTx2Inputs.Packet.logical",
  "NNH_CorrectTx2Inputs.Packet.mk",
  "NNH_CorrectTx2Inputs.Packet.proof",
  "NNH_CorrectTx2Inputs.Packet.proofAccount",
  "NNH_CorrectTx2Inputs.Packet.proof_eq",
  "NNH_CorrectTx2Inputs.Packet.proof_index",
  "NNH_CorrectTx2Inputs.Packet.proof_read",
  "NNH_CorrectTx2Inputs.Packet.public_eq",
  "NNH_CorrectTx2Inputs.Packet.validate",
  "NNH_CorrectTx2Inputs.Packet.validated",
  "NNH_CorrectTx2Inputs.Packet.validated_eq",
  "NNH_CorrectTx2Inputs.getters",
  "NNH_CorrectTx2Inputs.produce",
  "NNH_CorrectTx2Inputs.sdk",
  "NNH_DistinctPort.value",
  "NNH_EncodeOk.sdk",
  "NNH_ExactRemainingTypes.tx2Op11",
  "NNH_GetterOk.value",
  "NNH_Libraries.D",
  "NNH_MRegistryOps.install",
  "NNH_PdaOk.native",
  "NNH_RequestGuards.value",
  "NNH_S1CodecOk.decode",
  "NNH_Stage2Cut.Packet",
  "NNH_Stage2Cut.Packet.auth_ok",
  "NNH_Stage2Cut.Packet.checkpoint_account",
  "NNH_Stage2Cut.Packet.checkpoint_data",
  "NNH_Stage2Cut.Packet.checkpoint_index",
  "NNH_Stage2Cut.Packet.checkpoint_ok",
  "NNH_Stage2Cut.Packet.emit_ok",
  "NNH_Stage2Cut.Packet.encode_ok",
  "NNH_Stage2Cut.Packet.guards",
  "NNH_Stage2Cut.Packet.mk",
  "NNH_Stage2Cut.Packet.proof_account",
  "NNH_Stage2Cut.Packet.proof_data",
  "NNH_Stage2Cut.Packet.proof_index",
  "NNH_Stage2Cut.Packet.proof_length",
  "NNH_Stage2Cut.Packet.proof_ok",
  "NNH_Stage2Cut.Packet.public_bytes",
  "NNH_Stage2Cut.Packet.validate_ok",
  "NNH_Stage2Cut.Packet.validated",
  "NNH_Stage2GuardedCut.Packet",
  "NNH_Stage2GuardedCut.Packet.cut",
  "NNH_Stage2GuardedCut.Packet.domain",
  "NNH_Stage2GuardedCut.Packet.mk",
  "NNH_Stage2GuardedCut.produce",
  "NNH_Stage2GuardedEval.returned",
  "NNH_Stage2GuardedEval.value",
  "NNH_Stage2HeadGuard.equal",
  "NNH_Stage2HeadPort.source",
  "NNH_Stage2To064.source",
  "NNH_Tx1RouteCompare.source",
  "NNH_Tx2CheckpointPort.reinstall",
  "NNH_Tx2CheckpointPort.value",
  "NNH_Tx2Configuration.configuration",
  "NNH_Tx2Configuration.readonly",
  "NNH_Tx2Configuration.sdk",
  "NNH_Tx2Configuration.select",
  "NNH_Tx2ModelSlots.install",
  "NNH_Tx2RegistryPort.same",
  "NNH_Tx2RegistryPort.value",
  "NNH_ValidateScanStep.source",
  "NNH_ValidateSdkHeadStep.source",
  "NNH_ValidateSdkPort.value",
  "NNH_ValidateSdkTail.source",
  "NNH_ValidateTailPort.value",
  "NNH_ValidatedExtent.value",
  "NNS_Fold241.D",
  "NNS_Fold241.fold",
  "NNS_PortLaw241.replay_same",
  "NNS_PortLaw241.root",
  "NNT_Field.Required",
  "NNT_Field.r241",
  "NNT_Native241.D",
  "NNT_Native241.full",
  "NNT_Port241.root",
  "NNT_RelReplay241.fold",
  "NNT_Root241.parametric",
  "NOC_Stage1Conv.child",
  "NOC_Stage1Conv.codec",
  "NOC_Stage1Conv.conv",
  "NOC_Stage1Conv.fd11",
  "NOC_Stage1Conv.gate",
  "NOC_Stage1Conv.guards",
  "NOC_Stage1Conv.kOf",
  "NOC_Stage1Conv.routeData",
  "NOC_Stage1Conv.shapeOf",
  "NOC_Stage1Forward.S",
  "NOC_Stage1Forward.body",
  "NOC_Stage1Forward.ckLemma",
  "NOC_Stage1Forward.cmpLemma",
  "NOC_Stage1Forward.fdLemma",
  "NOC_Stage1Forward.gateLemma",
  "NOC_Stage1Forward.ok345",
  "NOC_Stage1Inv.Facts",
  "NOC_Stage1Inv.Facts.cb",
  "NOC_Stage1Inv.Facts.cka",
  "NOC_Stage1Inv.Facts.d1v",
  "NOC_Stage1Inv.Facts.enc",
  "NOC_Stage1Inv.Facts.h21",
  "NOC_Stage1Inv.Facts.hcb",
  "NOC_Stage1Inv.Facts.hck",
  "NOC_Stage1Inv.Facts.hcmp",
  "NOC_Stage1Inv.Facts.hd1",
  "NOC_Stage1Inv.Facts.hdec",
  "NOC_Stage1Inv.Facts.hdist",
  "NOC_Stage1Inv.Facts.hfd",
  "NOC_Stage1Inv.Facts.hkk",
  "NOC_Stage1Inv.Facts.hl",
  "NOC_Stage1Inv.Facts.hlen",
  "NOC_Stage1Inv.Facts.hne",
  "NOC_Stage1Inv.Facts.hpb",
  "NOC_Stage1Inv.Facts.hrbP",
  "NOC_Stage1Inv.Facts.hrbU",
  "NOC_Stage1Inv.Facts.hs0",
  "NOC_Stage1Inv.Facts.hs1",
  "NOC_Stage1Inv.Facts.hsp",
  "NOC_Stage1Inv.Facts.hsv",
  "NOC_Stage1Inv.Facts.htag",
  "NOC_Stage1Inv.Facts.htv",
  "NOC_Stage1Inv.Facts.hub",
  "NOC_Stage1Inv.Facts.hz",
  "NOC_Stage1Inv.Facts.i0",
  "NOC_Stage1Inv.Facts.i1",
  "NOC_Stage1Inv.Facts.i2",
  "NOC_Stage1Inv.Facts.kk",
  "NOC_Stage1Inv.Facts.mk",
  "NOC_Stage1Inv.Facts.nat",
  "NOC_Stage1Inv.Facts.pa",
  "NOC_Stage1Inv.Facts.pb",
  "NOC_Stage1Inv.Facts.pba",
  "NOC_Stage1Inv.Facts.s0",
  "NOC_Stage1Inv.Facts.s1",
  "NOC_Stage1Inv.Facts.sp",
  "NOC_Stage1Inv.Facts.st",
  "NOC_Stage1Inv.Facts.t",
  "NOC_Stage1Inv.Facts.ub",
  "NOC_Stage1Inv.S",
  "NOC_Stage1Inv.invert"]
def leaves : Array String := #["NNH_MRegistryOps.install",
  "NHY_PolicyModel.policy",
  "NJQ_Checkpoint.model",
  "NJQ_Master.model",
  "NJI_MasterModel.model",
  "NJI_MasterModel.terminal",
  "NJI_V1Models.Z",
  "NGL_CheckpointModel.install",
  "AspisR1.Port3_FinishStage.ne",
  "AspisR1.Hist_Authority.keyEq",
  "AspisR1.Port4B_CountInstall.nodeCount",
  "AspisR1.Port3_BatchStd.sameLeaf"]
def idDep : Array String := #["AspisR1.ARQ_BankCut.checkpoint",
  "AspisR1.ARS_Coverage.SupportedEntry",
  "AspisR1.ARS_Coverage.SupportedEntry.RuntimePersistence",
  "AspisR1.ARS_Coverage.SupportedEntry.accepted1",
  "AspisR1.ARS_Coverage.SupportedEntry.accepted2",
  "AspisR1.ARS_Coverage.SupportedEntry.actions",
  "AspisR1.ARS_Coverage.SupportedEntry.admission1",
  "AspisR1.ARS_Coverage.SupportedEntry.admission2",
  "AspisR1.ARS_Coverage.SupportedEntry.final1",
  "AspisR1.ARS_Coverage.SupportedEntry.final2",
  "AspisR1.ARS_Coverage.SupportedEntry.game",
  "AspisR1.ARS_Coverage.SupportedEntry.mk",
  "AspisR1.ARS_Coverage.SupportedEntry.p",
  "AspisR1.ARS_Coverage.SupportedEntry.post1",
  "AspisR1.ARS_Coverage.SupportedEntry.post2",
  "AspisR1.ARS_Coverage.SupportedEntry.saved",
  "AspisR1.ARS_Coverage.SupportedEntry.t",
  "AspisR1.ARS_Coverage.SupportedEntry.u",
  "AspisR1.ARS_Coverage.SupportedEntry.w1",
  "AspisR1.ARS_Coverage.SupportedEntry.w2",
  "AspisR1.ARU_CutsOrigin.selected",
  "AspisR1.ARU_Factory.deployed",
  "AspisR1.ARU_PartialAccepted.accepted",
  "AspisR1.ARU_PartialFactory.original",
  "AspisR1.ARU_Replies.accepted",
  "AspisR1.ARU_Selector.selected",
  "AspisR1.ARU_SourceResults.accepted",
  "AspisR1.ARU_Support.At",
  "AspisR1.ARU_Support.At.entry",
  "AspisR1.ARU_Support.At.firstAgrees",
  "AspisR1.ARU_Support.At.mk",
  "AspisR1.ARU_Support.At.secondAgrees",
  "AspisR1.ARV_FirstPartial.accepted",
  "AspisR1.ARW_AdmittedBudget.issued",
  "AspisR1.ARW_AdmittedQueries.admitted",
  "AspisR1.ARX_AdmittedRuntime.evaluation",
  "AspisR1.ARX_AdmittedRuntime.on_admitted",
  "AspisR1.ARX_AdmittedRuntime.outside",
  "AspisR1.ARX_AdmittedRuntime.permitted",
  "AspisR1.ARX_AdmittedRuntime.permitted_iff",
  "AspisR1.ARX_AdmittedRuntime.runtime",
  "AspisR1.ARX_SourceAlternative.accepted",
  "AspisR1.CPH_Program.not_system",
  "AspisR1.DGP_HostDigest.O1",
  "AspisR1.DGP_HostDigest.O2",
  "AspisR1.DGP_HostDigest.digestSource",
  "AspisR1.FIs_Rc7_Native.accepted",
  "AspisR1.FJp_ARCore.observations",
  "AspisR1.FJp_AccountJoin.accepted",
  "AspisR1.FJp_Domination.pointwise",
  "AspisR1.FJp_Mass.bounded",
  "AspisR1.FJp_Observations.observations",
  "AspisR1.FJp_Residual.numeric",
  "AspisR1.FJp_Ret_Rc7Native.accepted",
  "AspisR1.FJv_DFinalSource.source",
  "AspisR1.FJv_DFinalSource.source.match_1",
  "AspisR1.FJv_DNativeAccepted.accepted",
  "AspisR1.FJv_Observations.observations",
  "AspisR1.FJv_Top.deployed",
  "AspisR1.NNC_ActualChoices.selected",
  "AspisR1.NNC_RecSelect.selects",
  "AspisR1.NNH8_Acceptance.a3",
  "AspisR1.NNH8_Acceptance.a4",
  "AspisR1.NNH8_Acceptance.a5",
  "AspisR1.NNH8_ChargeOf.deployed_charge_of",
  "AspisR1.NNH8_DeployedOuter",
  "AspisR1.NNH8_DeployedOuterOf",
  "AspisR1.NNH8_Exec.ERec",
  "AspisR1.NNH8_Exec.clockFree",
  "AspisR1.NNH8_Exec.exec",
  "AspisR1.NNH8_Exec.exec._proof_1",
  "AspisR1.NNH8_Exec.exec._proof_2",
  "AspisR1.NNH8_Exec.exec._proof_3",
  "AspisR1.NNH8_Exec.recSelect",
  "AspisR1.NNH8_Exec.recSig",
  "AspisR1.NNH8_FirstWriter.oracle",
  "AspisR1.NNH8_FirstWriter.owned",
  "AspisR1.NNH8_FirstWriter.writer",
  "AspisR1.NNH8_FullSpace.same_event",
  "AspisR1.NNH8_Headline.headline",
  "AspisR1.NNH8_HeadlineB.headlineB",
  "AspisR1.NNH8_HeadlineB.headlineB._proof_1",
  "AspisR1.NNH8_HeadlineB.outcomeRec",
  "AspisR1.NNH8_HostCharge.bound",
  "AspisR1.NNH8_HostCharge.event_fixed",
  "AspisR1.NNH8_NMF.Associated",
  "AspisR1.NNH8_NMF.S",
  "AspisR1.NNH8_NMF.eventImage",
  "AspisR1.NNH8_NMF.nmfB",
  "AspisR1.NNH8_NMF.recSig",
  "AspisR1.NNH8_NMF.rootImage",
  "AspisR1.NNH8_NMF.selected",
  "AspisR1.NNH8_NMF.selected.match_1",
  "AspisR1.NNH8_NativeCuts.Packet",
  "AspisR1.NNH8_NativeCuts.Packet.cuts",
  "AspisR1.NNH8_NativeCuts.Packet.domain",
  "AspisR1.NNH8_NativeCuts.Packet.events",
  "AspisR1.NNH8_NativeCuts.Packet.f",
  "AspisR1.NNH8_NativeCuts.Packet.mk",
  "AspisR1.NNH8_NativeCuts.Packet.native",
  "AspisR1.NNH8_NativeCuts.Packet.origin",
  "AspisR1.NNH8_NativeCuts.Packet.persisted",
  "AspisR1.NNH8_NativeCuts.Packet.records",
  "AspisR1.NNH8_NativeCuts.Packet.s",
  "AspisR1.NNH8_NativeCuts.Packet.writerHeader",
  "AspisR1.NNH8_NativeCuts.Packet.writerRoot",
  "AspisR1.NNH8_NativeCuts.produce",
  "AspisR1.NNH8_Numeric.host_bound",
  "AspisR1.NNH8_Outer.inclusion",
  "AspisR1.NNH8_Packet.Cut",
  "AspisR1.NNH8_Packet.cuts",
  "AspisR1.NNH8_Packet.packet",
  "AspisR1.NNH8_Packet.packet._proof_1",
  "AspisR1.NNH8_Packet.packet._proof_2",
  "AspisR1.NNH8_Packet.packet._proof_3",
  "AspisR1.NNH8_Packet.packet._proof_4",
  "AspisR1.NNH8_Packet.packet._proof_5",
  "AspisR1.NNH8_Packet.packet._proof_6",
  "AspisR1.NNH8_Packet.packet._proof_7",
  "AspisR1.NNH8_Packet.packet._proof_8",
  "AspisR1.NNH8_Packet.select",
  "AspisR1.NNH8_Packet.source",
  "AspisR1.NNH8_Persistence.key",
  "AspisR1.NNH8_Persistence.persisted",
  "AspisR1.NNH8_Physical.deployed_splitB_of",
  "AspisR1.NNH8_Producers.accepted",
  "AspisR1.NNH8_Producers.game",
  "AspisR1.NNH8_Producers.origin",
  "AspisR1.NNH8_Producers.produce",
  "AspisR1.NNH8_ProtCells.produce",
  "AspisR1.NNH8_ProtLamports.produce",
  "AspisR1.NNH8_ProtMarker.produce",
  "AspisR1.NNH8_ProtOwner.produce",
  "AspisR1.NNH8_ProtPositive.produce",
  "AspisR1.NNH8_ProtPreserves.produce",
  "AspisR1.NNH8_Protection.produce",
  "AspisR1.NNH8_RecorderFixed.base",
  "AspisR1.NNH8_RecorderFixed.fixed",
  "AspisR1.NNH8_RecorderFixed.fixedProgram",
  "AspisR1.NNH8_RecorderFixed.program",
  "AspisR1.NNH8_Rest.Delivered",
  "AspisR1.NNH8_Rest.assemble",
  "AspisR1.NNH8_RestClaims.Goal",
  "AspisR1.NNH8_RestClaims.produce",
  "AspisR1.NNH8_RestCopy.CopyFacts",
  "AspisR1.NNH8_RestCopy.produce",
  "AspisR1.NNH8_RestEvents.produce",
  "AspisR1.NNH8_RestInstallation.produce",
  "AspisR1.NNH8_RestRecorder.produce",
  "AspisR1.NNH8_RestSetup.Goal",
  "AspisR1.NNH8_RestSetup.produce",
  "AspisR1.NNH8_RestTrace.produce",
  "AspisR1.NNH8_Retime.first",
  "AspisR1.NNH8_Retime.missing",
  "AspisR1.NNH8_Retime.sdk_same",
  "AspisR1.NNH8_Retime.second",
  "AspisR1.NNH8_Split.conclusion_iff",
  "AspisR1.NNH8_Split.outcome",
  "AspisR1.NNH8_Split.rest",
  "AspisR1.NNH8_Top.deployed_splitB_of",
  "AspisR1.NNH8_TopHost.R",
  "AspisR1.NNH8_TopHost.RestLaw",
  "AspisR1.NNH8_TopHost.S",
  "AspisR1.NNH8_TopHost.X",
  "AspisR1.NNH8_TopHost.g1a",
  "AspisR1.NNH8_TopHost.nmfB",
  "AspisR1.NNH8_TopHost.split",
  "AspisR1.NNH8_Weak241.inputs",
  "AspisR1.NNH_DigestSyntaxTransport.o1",
  "AspisR1.NNH_HostCtx.base",
  "AspisR1.NNH_HostCtx.configuration",
  "AspisR1.NNH_HostCtx.missing",
  "AspisR1.NNH_HostCtx.missingLit",
  "AspisR1.NNH_HostCtx.sdk",
  "AspisR1.NNH_HostWeak241.reference",
  "AspisR1.NNH_OutcomeRecAccepted.accepted",
  "AspisR1.NNH_RecordedCharge.bound",
  "AspisR1.NNH_RecordedCharge.recorder",
  "AspisR1.NNH_RecordedCharge.source",
  "AspisR1.NNH_ResultPortTransport.finish",
  "AspisR1.NNH_Run5bCtx.configuration",
  "AspisR1.NNH_Run5bCtx.sdk",
  "AspisR1.NNH_Run5bCurrentExpand.semantic",
  "AspisR1.NNH_Run5bCurrentExpand.semantic_slot",
  "AspisR1.NNH_Run5bCurrentInitial.returned",
  "AspisR1.NNH_Run5bCurrentInitial.slot",
  "AspisR1.NNH_Run5bCurrentInventory.adapter",
  "AspisR1.NNH_Run5bCurrentPending.source",
  "AspisR1.NNH_Run5bCurrentShape.current",
  "AspisR1.NNH_Run5bCurrentShape.parse",
  "AspisR1.NNH_Run5bCurrentShape.slot",
  "AspisR1.NNH_Run5bCurrentView.returned",
  "AspisR1.NNH_Run5bCurrentView.slot",
  "AspisR1.NNH_Run5bFinishEdge.selected",
  "AspisR1.NNH_Run5bGeometryMap.source",
  "AspisR1.NNH_Run5bGeometryReverse.selected",
  "AspisR1.NNH_Run5bGeometrySlots.double",
  "AspisR1.NNH_Run5bGeometrySlots.inverse",
  "AspisR1.NNH_Run5bGeometrySlots.line",
  "AspisR1.NNH_Run5bGeometrySlots.multiply",
  "AspisR1.NNH_Run5bGeometrySlots.one",
  "AspisR1.NNH_Run5bGeometrySlots.ops",
  "AspisR1.NNH_Run5bGeometrySlots.point",
  "AspisR1.NNH_Run5bGeometrySlots.subtract",
  "AspisR1.NNH_Run5bPreparedModel.source",
  "AspisR1.NNH_Run5bPreparedSlot.fixed",
  "AspisR1.NNH_Run5bQuerySlots.actual",
  "AspisR1.NNH_Run5bQuerySlots.circle",
  "AspisR1.NNH_Run5bQuerySlots.decode",
  "AspisR1.NNH_Run5bQuerySlots.dots",
  "AspisR1.NNH_Run5bQuerySlots.geometry",
  "AspisR1.NNH_Run5bQuerySlots.line",
  "AspisR1.NNH_Run6Fields.I",
  "AspisR1.NNH_Run6Fields.children",
  "AspisR1.NNH_Run6Fields.install",
  "AspisR1.NNH_Run6Fields.nmm",
  "AspisR1.NNH_Run6Fields.nmo",
  "AspisR1.NNH_Run6Fields.nmp",
  "AspisR1.NNH_Run6Fields.nms",
  "AspisR1.NNH_Run6Fields.nmt",
  "AspisR1.NNH_Run6Fields.nmv",
  "AspisR1.NNH_Run6Fields.nmw",
  "AspisR1.NNH_Run6Fields.nmx",
  "AspisR1.NNH_Run6Installed.implementation",
  "AspisR1.NNH_Run6ReaderNative.native",
  "AspisR1.NNH_StateSelect.selects",
  "AspisR1.NNH_Tx2LiteralSlots.constants",
  "AspisR1.NNH_Tx2LiteralSlots.pending",
  "AspisR1.NNH_Tx2LiteralSlots.powers",
  "AspisR1.NNH_Tx2SlotTransport.finish_slot",
  "AspisR1.NNH_Tx2SlotTransport.geometry_slot",
  "AspisR1.NNH_Tx2SlotTransport.stage",
  "AspisR1.NNH_Weak241Prefix.Packet",
  "AspisR1.NNH_Weak241Prefix.Packet.encode_ok",
  "AspisR1.NNH_Weak241Prefix.Packet.mk",
  "AspisR1.NNH_Weak241Prefix.Packet.n_eq",
  "AspisR1.NNH_Weak241Prefix.Packet.reads",
  "AspisR1.NNH_Weak241Prefix.Packet.validate_ok",
  "AspisR1.NNH_Weak241Prefix.Packet.validated",
  "AspisR1.NNH_Weak241Prefix.produce",
  "AspisR1.NNH_WeakReaderCuts.produce",
  "AspisR1.NNH_WeakTx2Inputs.Packet",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpoint",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpointAccount",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpoint_eq",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpoint_index",
  "AspisR1.NNH_WeakTx2Inputs.Packet.checkpoint_read",
  "AspisR1.NNH_WeakTx2Inputs.Packet.encode",
  "AspisR1.NNH_WeakTx2Inputs.Packet.encoded",
  "AspisR1.NNH_WeakTx2Inputs.Packet.extent",
  "AspisR1.NNH_WeakTx2Inputs.Packet.logical",
  "AspisR1.NNH_WeakTx2Inputs.Packet.mk",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proof",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proofAccount",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proof_eq",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proof_index",
  "AspisR1.NNH_WeakTx2Inputs.Packet.proof_read",
  "AspisR1.NNH_WeakTx2Inputs.Packet.public_eq",
  "AspisR1.NNH_WeakTx2Inputs.Packet.validate",
  "AspisR1.NNH_WeakTx2Inputs.Packet.validated",
  "AspisR1.NNH_WeakTx2Inputs.produce",
  "AspisR1.NNQ_HostDigest.o2",
  "AspisR1.NNQ_HostDigest.split",
  "AspisR1.NNR_ClockFree.modelSlots",
  "AspisR1.NNU_Geometry.source",
  "AspisR1.NNU_GeometrySelected.gather",
  "AspisR1.NNU_GeometrySelected.prefixCall",
  "AspisR1.NNU_GeometrySelected.zero",
  "AspisR1.NNU_GeometryTraversal.selected_loop",
  "AspisR1.NNU_GeometryTraversal.selected_step",
  "AspisR1.NNU_MerkleSlots.installed",
  "AspisR1.NNU_Query.source",
  "AspisR1.NNU_QueryAccum.power",
  "AspisR1.NNU_QueryAccum.product",
  "AspisR1.NNU_QueryAccum.slots",
  "AspisR1.NNU_QueryAccum.source",
  "AspisR1.NNU_QueryAccum.sum",
  "AspisR1.NNU_QueryLoop.finite",
  "AspisR1.NNU_QueryLoop.source",
  "AspisR1.NNU_QueryValues.source",
  "AspisR1.NNU_Stage2Tail.emitPacket",
  "AspisR1.NNU_Stage2Tail.returnedCuts",
  "AspisR1.NNV_AdapterEncodeHost.slot",
  "AspisR1.NNV_CheckpointDigest.source",
  "AspisR1.NNV_CurrentCheckpoint.slot",
  "AspisR1.NNV_CurrentCheckpoint.source",
  "AspisR1.NNV_CurrentFlush.returned",
  "AspisR1.NNV_CurrentFlush.slot",
  "AspisR1.NNV_CurrentGeometry.returned",
  "AspisR1.NNV_CurrentGeometry.slot",
  "AspisR1.NNV_CurrentGeometry.source",
  "AspisR1.NNV_CurrentQuerySource.slot",
  "AspisR1.NNV_CurrentQuerySource.source",
  "AspisR1.NNV_CurrentScan.returned",
  "AspisR1.NNV_CurrentScan.slot",
  "AspisR1.NNV_CurrentScan.source",
  "AspisR1.NNV_GeometryBody.source",
  "AspisR1.NNV_GeometryEq.source",
  "AspisR1.NNV_GeometryIndexPorts.first",
  "AspisR1.NNV_GeometryOuter.loop",
  "AspisR1.NNV_GeometryOuter.source",
  "AspisR1.NNV_GeometryOuter.stage",
  "AspisR1.NNV_GeometryPrefixSelected.source",
  "AspisR1.NNV_GeometryQuery.fibre",
  "AspisR1.NNV_GeometryQuery.source",
  "AspisR1.NNV_GeometrySelectedStd.any",
  "AspisR1.NNV_GeometrySelectedStd.array",
  "AspisR1.NNV_GeometrySelectedStd.base",
  "AspisR1.NNV_GeometrySelectedStd.empty",
  "AspisR1.NNV_GeometrySelectedStd.iterator",
  "AspisR1.NNV_GeometrySelectedStd.mapped",
  "AspisR1.NNV_GeometrySelectedStd.zero",
  "AspisR1.NNV_GeometryTerminal.source",
  "AspisR1.NNV_PrepareView.returned",
  "AspisR1.NNV_PreparedAtHost.digest",
  "AspisR1.NNV_PreparedAtHost.source",
  "AspisR1.NNX_CommonEncode.source",
  "AspisR1.NNX_CurrentQuery.actual",
  "AspisR1.NNX_CurrentQuery.slots",
  "AspisR1.NNX_CurrentQuery.source",
  "AspisR1.NNX_Flush.source",
  "AspisR1.NNX_LeafAgreement.source",
  "AspisR1.NNX_PreparedValue.source",
  "AspisR1.NNY_NNUParent.parent",
  "AspisR1.NNY_ParserAssociation.source",
  "AspisR1.NNY_Stage2PacketResidual.returned",
  "AspisR1.NOC_Conv094.accNew",
  "AspisR1.NOC_Conv094.geometry",
  "AspisR1.NOC_Conv094.scan",
  "AspisR1.NOC_Conv094.weightsNew",
  "AspisR1.NOC_ConvLeaves.cur",
  "AspisR1.NOC_ConvLeaves.filled",
  "AspisR1.NOC_ConvLeaves.parse",
  "AspisR1.NOC_ConvLeaves.prepared",
  "AspisR1.NOC_ConvLeaves.view",
  "AspisR1.NOC_HostCtx.Exhibited",
  "AspisR1.NOC_HostCtx.base",
  "AspisR1.NOC_HostCtx.configuration",
  "AspisR1.NOC_HostCtx.extraction",
  "AspisR1.NOC_HostCtx.missing",
  "AspisR1.NOC_HostCtx.missingLit",
  "AspisR1.NOC_HostCtx.model1",
  "AspisR1.NOC_HostCtx.model2",
  "AspisR1.NOC_HostCtx.sdk",
  "AspisR1.NOC_MerkleBounded.host",
  "AspisR1.NOC_MerkleBounded.hostNode",
  "AspisR1.NOC_MerkleBounded.hostParent",
  "AspisR1.NOC_Op9.op9",
  "AspisR1.NOC_Op9Slot.digest",
  "AspisR1.NOC_Op9Slot.slot",
  "AspisR1.NOC_PrepareConv.cur",
  "AspisR1.NOC_PrepareConv.prepare",
  "AspisR1.NOC_PrepareFront.cur",
  "AspisR1.NOC_PrepareFront.filled",
  "AspisR1.NOC_PrepareFront.logical_semantic",
  "AspisR1.NOC_PrepareFront.off_inactive",
  "AspisR1.NOC_PrepareFront.off_semantic",
  "AspisR1.NOC_PrepareFront.off_y1",
  "AspisR1.NOC_PrepareFront.source",
  "AspisR1.NOC_QueryLink.current",
  "AspisR1.NOC_Run5bClaims.conclusion",
  "AspisR1.NOC_Run5bCtx.Exhibited",
  "AspisR1.NOC_Run5bCtx.base",
  "AspisR1.NOC_Run5bCtx.configuration",
  "AspisR1.NOC_Run5bCtx.extraction",
  "AspisR1.NOC_Run5bCtx.missing",
  "AspisR1.NOC_Run5bCtx.model1",
  "AspisR1.NOC_Run5bCtx.model2",
  "AspisR1.NOC_Run5bCtx.sdk",
  "AspisR1.NOC_Run5bHost.S_host",
  "AspisR1.NOC_Run5bHost.S_host._proof_1",
  "AspisR1.NOC_Run5bHost.a0",
  "AspisR1.NOC_Run5bHost.bound",
  "AspisR1.NOC_Run5bHost.data",
  "AspisR1.NOC_Run5bHost.envSig",
  "AspisR1.NOC_Run5bHost.event",
  "AspisR1.NOC_Run5bHost.r0",
  "AspisR1.NOC_Run5bHost.record",
  "AspisR1.NOC_Run5bHost.runtime",
  "AspisR1.NOC_Run5bHost.seed",
  "AspisR1.NOC_SeedTransfer.newCfg",
  "AspisR1.NOC_SeedTransfer.op9",
  "AspisR1.NOC_SemConv.op9",
  "AspisR1.NOC_Stage1Iff.clockFree",
  "AspisR1.NOC_Stage1Iff.iff345",
  "AspisR1.NOC_Stage1Iff.sameSdk",
  "AspisR1.NOC_Stage1Iff.sdk_at_slot",
  "AspisR1.NOC_Tx1Conv.batch",
  "AspisR1.NOC_Tx1Conv.cur",
  "AspisR1.NOC_Tx1Conv.query",
  "AspisR1.NOC_Tx1Conv.tx1",
  "AspisR1.NOC_Tx1Forward.batch",
  "AspisR1.NOC_Tx1Forward.cur",
  "AspisR1.NOC_Tx1Forward.off_folded",
  "AspisR1.NOC_Tx1Forward.off_round1",
  "AspisR1.NOC_Tx1Forward.query",
  "AspisR1.NOC_Tx1Forward.source",
  "AspisR1.NOC_Tx1Forward.zero",
  "AspisR1.NOF_A2FieldCorrected.clockFree",
  "AspisR1.NOF_A2FieldCorrected.field",
  "AspisR1.NOF_A2FieldCorrected.sdk_at_slot",
  "AspisR1.NOF_CommonConverse.common",
  "AspisR1.NOF_CommonConverse.source",
  "AspisR1.NOF_CommonConverse.source_run",
  "AspisR1.NOF_CommonConverse.tail_transport",
  "AspisR1.NOF_Tx2Op11.tx2Op11",
  "AspisR1.NOM_MerkleParent.hostParent",
  "AspisR1.NOQ_A1Assembly.IFF",
  "AspisR1.NOQ_A1Assembly.errT",
  "AspisR1.NOQ_A1Assembly.field_of",
  "AspisR1.NOQ_A1Assembly.okT",
  "AspisR1.NOQ_FinalCombined.field",
  "AspisR1.NOQ_WeakErrHost.modelRet1",
  "AspisR1.RPx_Deployed.deployed",
  "AspisR1.TAS_FinalB.deployed_charge",
  "AspisR1.TAS_FinalB.deployed_splitB",
  "AspisR1.TAS_FinalB.fail_sub_rec",
  "LIBB_PoolLib.deployed",
  "LIB_Deployed.deployed",
  "LIB_Deployed.ids",
  "LIB_Instances.D",
  "NHJ_IdPacket.pool",
  "NHJ_IdPacket.registry",
  "NMS_R2AfterAuth242.factor",
  "NMS_R2AfterAuthEq242.factor",
  "NMS_R2Gated242.source",
  "NMS_R2N_Native242Children.children",
  "NMS_R2N_Native242Children.meaning",
  "NMS_R2RequestBindings.pool",
  "NMS_R2RequestGuards.actual",
  "NMS_R2RequestGuards.bad",
  "NMS_R2RequestGuards.full",
  "NMS_R2RequestGuards.source",
  "NMX_R3_Instantiated233.native",
  "NMX_R3_Instantiated233.registry_packet",
  "NMX_R3_Instantiated233.represented",
  "NMX_R3_RegistryRoot.authenticate",
  "NMX_R3_RegistryRoot.root",
  "NMX_R4_AllArgs.execution",
  "NMX_R4_AllArgs.operational",
  "NMX_R4_Authentication.authenticate",
  "NMX_R4_Authentication.context",
  "NMX_R4_Authentication.observed",
  "NMX_R4_Authentication.root",
  "NMX_R4_NMS233.packet",
  "NMX_R4_NMS233.typed",
  "NMX_R4_NMS242Instantiation.fold",
  "NMX_R5_AfterAuth242.full",
  "NMX_R5_Decode242.full",
  "NMX_R5_Decode242.model",
  "NMX_R5_Decode242.source",
  "NMX_R5_Guards242.factor",
  "NMX_R5_Guards242.full",
  "NMX_R5_Guards242.model",
  "NMX_R5_Native242.full",
  "NMX_R5_PrefixSource242.body",
  "NMX_R5_PrefixSource242.full",
  "NMX_R5_Request242.D",
  "NMX_R5_Request242.bad",
  "NMX_R5_Request242.full",
  "NMX_R5_Request242.model",
  "NMX_R5_Slot242.D",
  "NMX_R5_Slot242.full",
  "NMX_R5_Slot242.model",
  "NMX_R5_Slot242.source",
  "NMX_R6_NativeLive242.live",
  "NMX_R6_NativeLive242.observation",
  "NMX_R6_NativeLive242.source_member",
  "NMX_R6_Nonempty.auth",
  "NMX_R6_Port242.D",
  "NMX_R6_Port242.replay_member",
  "NMX_R6_Port242.validate",
  "NMX_R6_Validation.root",
  "NMX_R6_Validation.validate",
  "NMX_R7_Port241.stage2",
  "NMX_R7_PortLaw241.replay_member",
  "NMX_R8_After241.full",
  "NMX_R8_AfterFactor241.factor",
  "NMX_R8_AfterFactor241.source",
  "NMX_R8_Children241.grouped",
  "NMX_R8_Children241.original",
  "NMX_R8_Children241.validate",
  "NMX_R8_Encoded241.full",
  "NMX_R8_EncodedFactor241.factor",
  "NMX_R8_GroupEncode241.source",
  "NMX_R8_GroupReads241.source",
  "NMX_R8_GroupValidate241.source",
  "NMX_R8_Reads241.full",
  "NMX_R8_ReadsFactor241.factor",
  "NMX_R8_ReadsFactor241.source",
  "NMX_R9_After241.fixed",
  "NMX_R9_After241.full",
  "NMX_R9_After241.grouped",
  "NMX_R9_Children241.grouped",
  "NMX_R9_Children241.original",
  "NMX_R9_Children241.validate",
  "NMX_R9_Children241.validate_full",
  "NMX_R9_GroupHead241.source",
  "NMX_R9_Head241.full",
  "NMX_R9_HeaderFactor241.factor",
  "NMX_R9_HeaderFactor241.later",
  "NMX_R9_HeaderFactor241.source",
  "NMX_R9_Live241.grouped",
  "NMX_R9_Live241.live",
  "NMX_R9_Live241.observation",
  "NMX_R9_Live241.source_member",
  "NMX_R9_Live241.validate",
  "NMX_R9_Native241.meaning",
  "NMX_R9_RelReplay241.D",
  "NMX_R9_RelReplay241.replay",
  "NMX_R9_StageTwo.D",
  "NMX_R9_StageTwo.stage2",
  "NMX_R9_ValidateUse241.full",
  "NMX_R9_ValidateUse241.source",
  "NNH_AuthCheckpointInputs.Packet",
  "NNH_AuthCheckpointInputs.Packet.checkpoint",
  "NNH_AuthCheckpointInputs.Packet.data",
  "NNH_AuthCheckpointInputs.Packet.decode",
  "NNH_AuthCheckpointInputs.Packet.domain_eq",
  "NNH_AuthCheckpointInputs.Packet.mk",
  "NNH_AuthCheckpointInputs.Packet.next",
  "NNH_AuthCheckpointInputs.Packet.pda",
  "NNH_AuthCheckpointInputs.Packet.pool_eq",
  "NNH_AuthCheckpointInputs.Packet.read",
  "NNH_AuthCheckpointInputs.produce",
  "NNH_AuthCheckpointPort.value",
  "NNH_AuthCheckpointStep.source",
  "NNH_AuthGuardPorts.data",
  "NNH_AuthGuardPorts.readonly",
  "NNH_AuthLaneInputs.Packet",
  "NNH_AuthLaneInputs.Packet.data",
  "NNH_AuthLaneInputs.Packet.decode",
  "NNH_AuthLaneInputs.Packet.lane_eq",
  "NNH_AuthLaneInputs.Packet.mk",
  "NNH_AuthLaneInputs.Packet.output",
  "NNH_AuthLaneInputs.Packet.pda",
  "NNH_AuthLaneInputs.Packet.pool_eq",
  "NNH_AuthLaneInputs.Packet.read",
  "NNH_AuthLaneInputs.Packet.state",
  "NNH_AuthLaneInputs.produce",
  "NNH_AuthLanePort.value",
  "NNH_AuthLaneStep.source",
  "NNH_AuthMasterInputs.Packet",
  "NNH_AuthMasterInputs.Packet.data",
  "NNH_AuthMasterInputs.Packet.decode",
  "NNH_AuthMasterInputs.Packet.mask_eq",
  "NNH_AuthMasterInputs.Packet.master",
  "NNH_AuthMasterInputs.Packet.mk",
  "NNH_AuthMasterInputs.Packet.next",
  "NNH_AuthMasterInputs.Packet.pda",
  "NNH_AuthMasterInputs.Packet.pool_eq",
  "NNH_AuthMasterInputs.Packet.read",
  "NNH_AuthMasterInputs.Packet.registry",
  "NNH_AuthMasterInputs.produce",
  "NNH_AuthMasterPort.value",
  "NNH_AuthMasterStep.source",
  "NNH_AuthNativeGuards.produce",
  "NNH_AuthSdkBodyPort.value",
  "NNH_AuthSdkDistinct.value",
  "NNH_AuthSdkGuards.produce",
  "NNH_AuthSdkPort.value",
  "NNH_AuthSdkTail.checkpoint",
  "NNH_AuthSdkTail.lane",
  "NNH_AuthSdkTail.master",
  "NNH_AuthSdkTail.registry",
  "NNH_AuthSlotFacts.ne_self",
  "NNH_CorrectCallInputs.produce",
  "NNH_CorrectConfiguration.configuration",
  "NNH_CorrectConfiguration.sdk",
  "NNH_CorrectExtents.value",
  "NNH_CorrectReads.source",
  "NNH_CorrectTx2Inputs.Packet",
  "NNH_CorrectTx2Inputs.Packet.checkpoint",
  "NNH_CorrectTx2Inputs.Packet.checkpointAccount",
  "NNH_CorrectTx2Inputs.Packet.checkpoint_eq",
  "NNH_CorrectTx2Inputs.Packet.checkpoint_index",
  "NNH_CorrectTx2Inputs.Packet.checkpoint_read",
  "NNH_CorrectTx2Inputs.Packet.encode",
  "NNH_CorrectTx2Inputs.Packet.encoded",
  "NNH_CorrectTx2Inputs.Packet.extent",
  "NNH_CorrectTx2Inputs.Packet.logical",
  "NNH_CorrectTx2Inputs.Packet.mk",
  "NNH_CorrectTx2Inputs.Packet.proof",
  "NNH_CorrectTx2Inputs.Packet.proofAccount",
  "NNH_CorrectTx2Inputs.Packet.proof_eq",
  "NNH_CorrectTx2Inputs.Packet.proof_index",
  "NNH_CorrectTx2Inputs.Packet.proof_read",
  "NNH_CorrectTx2Inputs.Packet.public_eq",
  "NNH_CorrectTx2Inputs.Packet.validate",
  "NNH_CorrectTx2Inputs.Packet.validated",
  "NNH_CorrectTx2Inputs.Packet.validated_eq",
  "NNH_CorrectTx2Inputs.getters",
  "NNH_CorrectTx2Inputs.produce",
  "NNH_CorrectTx2Inputs.sdk",
  "NNH_DistinctPort.value",
  "NNH_EncodeOk.sdk",
  "NNH_ExactRemainingTypes.tx2Op11",
  "NNH_GetterOk.value",
  "NNH_Libraries.D",
  "NNH_PdaOk.native",
  "NNH_RequestGuards.value",
  "NNH_S1CodecOk.decode",
  "NNH_Stage2Cut.Packet",
  "NNH_Stage2Cut.Packet.auth_ok",
  "NNH_Stage2Cut.Packet.checkpoint_account",
  "NNH_Stage2Cut.Packet.checkpoint_data",
  "NNH_Stage2Cut.Packet.checkpoint_index",
  "NNH_Stage2Cut.Packet.checkpoint_ok",
  "NNH_Stage2Cut.Packet.emit_ok",
  "NNH_Stage2Cut.Packet.encode_ok",
  "NNH_Stage2Cut.Packet.guards",
  "NNH_Stage2Cut.Packet.mk",
  "NNH_Stage2Cut.Packet.proof_account",
  "NNH_Stage2Cut.Packet.proof_data",
  "NNH_Stage2Cut.Packet.proof_index",
  "NNH_Stage2Cut.Packet.proof_length",
  "NNH_Stage2Cut.Packet.proof_ok",
  "NNH_Stage2Cut.Packet.public_bytes",
  "NNH_Stage2Cut.Packet.validate_ok",
  "NNH_Stage2Cut.Packet.validated",
  "NNH_Stage2GuardedCut.Packet",
  "NNH_Stage2GuardedCut.Packet.cut",
  "NNH_Stage2GuardedCut.Packet.domain",
  "NNH_Stage2GuardedCut.Packet.mk",
  "NNH_Stage2GuardedCut.produce",
  "NNH_Stage2GuardedEval.returned",
  "NNH_Stage2GuardedEval.value",
  "NNH_Stage2HeadGuard.equal",
  "NNH_Stage2HeadPort.source",
  "NNH_Stage2To064.source",
  "NNH_Tx1RouteCompare.source",
  "NNH_Tx2CheckpointPort.reinstall",
  "NNH_Tx2CheckpointPort.value",
  "NNH_Tx2Configuration.configuration",
  "NNH_Tx2Configuration.readonly",
  "NNH_Tx2Configuration.sdk",
  "NNH_Tx2Configuration.select",
  "NNH_Tx2ModelSlots.install",
  "NNH_Tx2RegistryPort.same",
  "NNH_Tx2RegistryPort.value",
  "NNH_ValidateScanStep.source",
  "NNH_ValidateSdkHeadStep.source",
  "NNH_ValidateSdkPort.value",
  "NNH_ValidateSdkTail.source",
  "NNH_ValidateTailPort.value",
  "NNH_ValidatedExtent.value",
  "NNS_Fold241.D",
  "NNS_Fold241.fold",
  "NNS_PortLaw241.replay_same",
  "NNS_PortLaw241.root",
  "NNT_Field.Required",
  "NNT_Field.r241",
  "NNT_Native241.D",
  "NNT_Native241.full",
  "NNT_Port241.root",
  "NNT_RelReplay241.fold",
  "NNT_Root241.parametric",
  "NOC_Stage1Conv.child",
  "NOC_Stage1Conv.codec",
  "NOC_Stage1Conv.conv",
  "NOC_Stage1Conv.fd11",
  "NOC_Stage1Conv.gate",
  "NOC_Stage1Conv.guards",
  "NOC_Stage1Conv.kOf",
  "NOC_Stage1Conv.routeData",
  "NOC_Stage1Conv.shapeOf",
  "NOC_Stage1Forward.S",
  "NOC_Stage1Forward.body",
  "NOC_Stage1Forward.ckLemma",
  "NOC_Stage1Forward.cmpLemma",
  "NOC_Stage1Forward.fdLemma",
  "NOC_Stage1Forward.gateLemma",
  "NOC_Stage1Forward.ok345",
  "NOC_Stage1Inv.Facts",
  "NOC_Stage1Inv.Facts.cb",
  "NOC_Stage1Inv.Facts.cka",
  "NOC_Stage1Inv.Facts.d1v",
  "NOC_Stage1Inv.Facts.enc",
  "NOC_Stage1Inv.Facts.h21",
  "NOC_Stage1Inv.Facts.hcb",
  "NOC_Stage1Inv.Facts.hck",
  "NOC_Stage1Inv.Facts.hcmp",
  "NOC_Stage1Inv.Facts.hd1",
  "NOC_Stage1Inv.Facts.hdec",
  "NOC_Stage1Inv.Facts.hdist",
  "NOC_Stage1Inv.Facts.hfd",
  "NOC_Stage1Inv.Facts.hkk",
  "NOC_Stage1Inv.Facts.hl",
  "NOC_Stage1Inv.Facts.hlen",
  "NOC_Stage1Inv.Facts.hne",
  "NOC_Stage1Inv.Facts.hpb",
  "NOC_Stage1Inv.Facts.hrbP",
  "NOC_Stage1Inv.Facts.hrbU",
  "NOC_Stage1Inv.Facts.hs0",
  "NOC_Stage1Inv.Facts.hs1",
  "NOC_Stage1Inv.Facts.hsp",
  "NOC_Stage1Inv.Facts.hsv",
  "NOC_Stage1Inv.Facts.htag",
  "NOC_Stage1Inv.Facts.htv",
  "NOC_Stage1Inv.Facts.hub",
  "NOC_Stage1Inv.Facts.hz",
  "NOC_Stage1Inv.Facts.i0",
  "NOC_Stage1Inv.Facts.i1",
  "NOC_Stage1Inv.Facts.i2",
  "NOC_Stage1Inv.Facts.kk",
  "NOC_Stage1Inv.Facts.mk",
  "NOC_Stage1Inv.Facts.nat",
  "NOC_Stage1Inv.Facts.pa",
  "NOC_Stage1Inv.Facts.pb",
  "NOC_Stage1Inv.Facts.pba",
  "NOC_Stage1Inv.Facts.s0",
  "NOC_Stage1Inv.Facts.s1",
  "NOC_Stage1Inv.Facts.sp",
  "NOC_Stage1Inv.Facts.st",
  "NOC_Stage1Inv.Facts.t",
  "NOC_Stage1Inv.Facts.ub",
  "NOC_Stage1Inv.S",
  "NOC_Stage1Inv.invert"]
def toSet (xs : Array String) : NameSet := xs.foldl (fun s x => s.insert x.toName) {}
def ids : Std.HashMap Name Name := Std.HashMap.ofList [
  (`AspisR1.CPH_Program.verifier, `NPO_DeployedIds.verifierNov),
  (`NHJ_IdPacket.poolDefault, `NPO_DeployedIds.poolNov),
  (`NHJ_IdPacket.registryDefault, `NPO_DeployedIds.registryNov)]
end NPP.Inputs

/-! Structural `DecidableEq` for the structure carriers of the remaining site (WideExact and the
field structures under it), by the standard deriving handler. These are new computable instances;
they add no axiom and change no existing declaration. -/
open Lean Elab Command Meta in
partial def NPP.deriveDecEq (S : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := getStructureInfo? env S | throwError "{S} is not a structure"
  let has ← liftTermElabM do
    let some ci := env.find? S | return true
    forallTelescope ci.type fun xs _ => do
      let ty := mkAppN (mkConst S (ci.levelParams.map Level.param)) xs
      return (← synthInstance? (← mkAppM ``DecidableEq #[ty])).isSome
  if has then return
  for f in info.fieldNames do
    let some pf := env.find? (S ++ f) | continue
    let heads ← liftTermElabM <| forallTelescope pf.type fun _ body => do
      let b ← whnf body
      return b.getAppFn.constName?
    if let some T := heads then
      if (getStructureInfo? env T).isSome && T != S then NPP.deriveDecEq T
  NPP.log <| Json.mkObj [("derive_DecidableEq", toJson S.toString)]
  elabCommand (← `(deriving instance DecidableEq for $(mkIdent S)))

run_cmd NPP.deriveDecEq `AspisR1Stage2.aspis_core.field.wide_exact.WideExact

open Lean Meta in
run_meta do
  let (copied, eqs) ← NPP.stageA `AspisR1.NOC_Run5bCtx.sdk (NPP.Inputs.toSet NPP.Inputs.cand)
    (NPP.Inputs.toSet NPP.Inputs.leaves) NPP.Inputs.ids (NPP.Inputs.toSet NPP.Inputs.idDep) `NPP_C
  NPP.log <| Json.mkObj [("event","stageA"),("copied", toJson copied.size),("eqs", toJson (eqs.map toString))]
  for e in eqs do
    let ax ← collectAxioms e
    NPP.log <| Json.mkObj [("axioms", toJson e.toString), ("value", toJson (ax.map toString))]
  for c in copied do
    NPP.log <| Json.mkObj [("copy", toJson c.toString), ("noncomputable", toJson (isNoncomputable (← getEnv) c)),
      ("ir", toJson ((Lean.IR.findEnvDecl (← getEnv) c).isSome))]
