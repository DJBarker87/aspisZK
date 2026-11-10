import Lean
/-! NPP_ re-pointing of NPN_RecordedFrame / NPN_RecordedHost to the 10 November host (native tool).
Target not yet established.

Imports NPO_CloneNov and NPN_RecordedHost. Every constant of the two NPN_ modules is visited in
dependency order. A constant is id-dependent if it reaches one of the three id constants
(AspisR1.CPH_Program.verifier, NHJ_IdPacket.poolDefault, NHJ_IdPacket.registryDefault) through
types, values or projections, over the whole environment. Every id-dependent non-NPN constant
reached must have an NPO_Nov copy (else the tool stops). Each id-dependent NPN constant `n` is
copied as `NPP_Nov ++ n` with every id-dependent reference renamed (non-NPN `X` to `NPO_Nov ++ X`,
NPN `m` to `NPP_Nov ++ m`) and sent to the kernel with `addDecl` (full checking). The statement
check: stripping the prefixes from a copy's type gives the original type exactly. Output
NPP_RecordedHostNov.olean (no IR). -/
open Lean Meta

namespace NPP_Repoint
def log (j : Json) : IO Unit := do IO.println j.compress; (← IO.getStdout).flush

unsafe def collect (e : Expr) : StateM (PtrSet Expr × NameSet) Unit := do
  if (← get).1.contains e then return
  modify fun (v, s) => (v.insert e, s)
  match e with
  | .const n _ => modify fun (v, s) => (v, s.insert n)
  | .proj s _ b => modify (fun (v, ns) => (v, ns.insert s)); collect b
  | .app f a => collect f; collect a
  | .lam _ d b _ | .forallE _ d b _ => collect d; collect b
  | .letE _ t v b _ => collect t; collect v; collect b
  | .mdata _ b => collect b
  | _ => pure ()
unsafe def usedImpl (es : List Expr) : NameSet :=
  let act : StateM (PtrSet Expr × NameSet) Unit := es.forM collect
  (act.run (mkPtrSet, {})).2.2
/-- constants and projection structures of `e` (NPO_Clone's pointer-set walker) -/
@[implemented_by usedImpl] opaque usedL (es : List Expr) : NameSet
def usedNames (e : Expr) : MetaM NameSet := pure (usedL [e])

def depsP (env : Environment) (ci : ConstantInfo) : NameSet :=
  match ci with
  | .inductInfo ii =>
    let ctorTys := ii.all.flatMap fun i => match env.find? i with
      | some (.inductInfo jj) => jj.ctors.filterMap fun c => (env.find? c).map (·.type)
      | _ => []
    let tys := ii.all.filterMap fun i => (env.find? i).map (·.type)
    (usedL (tys ++ ctorTys)).filter fun n => !(ii.all.contains n) && !(ii.ctors.contains n)
  | .ctorInfo c => (usedL [c.type]).insert c.induct
  | _ => match ci.value? (allowOpaque := true) with
    | some v => usedL [ci.type, v]
    | none => usedL [ci.type]

def depsOf (env : Environment) (ci : ConstantInfo) : MetaM NameSet := do
  match ci with
  | .inductInfo ii =>
    let mut s : NameSet := {}
    for i in ii.all do
      if let some (.inductInfo jj) := env.find? i then
        for x in (← usedNames jj.type).toList do s := s.insert x
        for c in jj.ctors do
          if let some cc := env.find? c then
            for x in (← usedNames cc.type).toList do s := s.insert x
    return s.filter fun n => !(ii.all.contains n) && !(ii.ctors.contains n)
  | .ctorInfo c => return (← usedNames c.type).insert c.induct
  | _ =>
    let s ← usedNames ci.type
    match ci.value? (allowOpaque := true) with
    | some v => return (← usedNames v).foldl (·.insert ·) s
    | none => return s

partial def subst (isDep : Name → Bool) (ren : Name → Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n us => if isDep n then some (.const (ren n) us) else none
    | .proj s i b => if isDep s then some (.proj (ren s) i (subst isDep ren b)) else none
    | _ => none

def unren (pre1 pre2 : Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n us =>
      if pre1.isPrefixOf n then some (.const (n.replacePrefix pre1 .anonymous) us)
      else if pre2.isPrefixOf n then some (.const (n.replacePrefix pre2 .anonymous) us) else none
    | _ => none

def run (outDir : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `NPO_CloneNov}, {module := `NPN_RecordedHost}] {} (trustLevel := 1024) (loadExts := false)
  let targets : NameSet := [`AspisR1.CPH_Program.verifier, `NHJ_IdPacket.poolDefault, `NHJ_IdPacket.registryDefault].foldl (·.insert ·) {}
  let npnMods := #[`NPN_RecordedFrame, `NPN_RecordedHost]
  let isNPN (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => npnMods.contains env.header.moduleNames[i.toNat]!
    | none => false
  log <| Json.mkObj [("event","imported"),("modules", toJson env.header.moduleNames.size)]
  let mut roots : List Name := []
  for i in [0:env.header.moduleNames.size] do
    if npnMods.contains env.header.moduleNames[i]! then
      roots := roots ++ env.header.moduleData[i]!.constNames.toList
  log <| Json.mkObj [("event","roots"),("npn_roots", toJson roots.length)]
  -- full id-dependence walk (post-order), in IO as in NPO_DepsMain (NPO_L005: 146,554 constants, 19 s)
  let t0 ← IO.monoMsNow
  let mut dep : Std.HashMap Name Bool := {}
  let mut started : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array (Name × Bool) := (roots.map (·, false)).toArray
  while h : stack.size > 0 do
    let (n, ex) := stack.back
    stack := stack.pop
    if dep.contains n then continue
    if targets.contains n then dep := dep.insert n true; continue
    match env.find? n with
    | none => dep := dep.insert n false
    | some ci =>
      let ds := depsP env ci
      if !ex then
        if started.contains n then continue
        started := started.insert n
        stack := stack.push (n, true)
        for d in ds do
          if !dep.contains d then stack := stack.push (d, false)
      else
        let b := ds.any (fun d => dep.getD d false)
        dep := dep.insert n b
        if isNPN n then order := order.push n
        if dep.size % 20000 == 0 then
          log <| Json.mkObj [("event","walk_progress"),("ms", toJson ((← IO.monoMsNow) - t0)),("done", toJson dep.size),("stack", toJson stack.size)]
  log <| Json.mkObj [("event","walk_done"),("ms", toJson ((← IO.monoMsNow) - t0)),("reachable", toJson dep.size)]
  let walked := (dep, order)
  let ctx : Core.Context := { fileName := "NPP_RecordedHostNov", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env := env.setMainModule `NPP_RecordedHostNov }
  let act : MetaM UInt32 := do
    let (dep, order) := walked
    let reached := dep.toList.filter (·.2) |>.map (·.1) |>.filter (fun n => !isNPN n && !targets.contains n)
    let missing := reached.filter fun n => !(env.contains (`NPO_Nov ++ n))
    log <| Json.mkObj [("event","walk"),("reachable", toJson dep.size),("npn_constants", toJson order.size),
      ("npn_id_dependent", toJson (order.filter (dep.getD · false)).size),
      ("non_npn_id_dependent_reached", toJson reached.length),("without_NPO_Nov_copy", toJson (missing.map toString))]
    if !missing.isEmpty then return 2
    let idMap : Std.HashMap Name Name := Std.HashMap.ofList [
      (`AspisR1.CPH_Program.verifier, `NPO_DeployedIds.verifierNov),
      (`NHJ_IdPacket.poolDefault, `NPO_DeployedIds.poolNov),
      (`NHJ_IdPacket.registryDefault, `NPO_DeployedIds.registryNov)]
    let isDep (n : Name) := dep.getD n false
    let ren (n : Name) : Name := match idMap[n]? with
      | some m => m
      | none => if isNPN n then `NPP_Nov ++ n else `NPO_Nov ++ n
    let sub := subst isDep ren
    let mut bad := 0
    let mut copied : Array Name := #[]
    for n in order do
      if !dep.getD n false then
        log <| Json.mkObj [("n", toJson n.toString),("status","unchanged (not id-dependent)")]
        continue
      let some ci := env.find? n | continue
      let cv (c : ConstantVal) : ConstantVal := { c with «name» := ren c.name, type := sub c.type }
      let decl? : Option Declaration := match ci with
        | .defnInfo v => some <| .defnDecl { v with toConstantVal := cv v.toConstantVal, value := sub v.value, all := v.all.map ren }
        | .thmInfo v => some <| .thmDecl { v with toConstantVal := cv v.toConstantVal, value := sub v.value, all := v.all.map ren }
        | _ => none
      let some d := decl? | log <| Json.mkObj [("n", toJson n.toString),("status","UNSUPPORTED kind")]; bad := bad + 1; continue
      try
        addDecl d
        copied := copied.push n
        let ty := (← getEnv).find? (ren n) |>.map (·.type) |>.getD (mkConst ``True)
        let back := (unren `NPO_Nov `NPP_Nov ty).replace fun x => match x with
          | .const c us => (idMap.toList.find? (·.2 == c)).map fun (o, _) => .const o us
          | _ => none
        let same := back == ci.type
        log <| Json.mkObj [("n", toJson n.toString),("copy", toJson (ren n).toString),("status","ok"),
          ("statement_equal_after_unrenaming", toJson same)]
        if !same then bad := bad + 1
      catch e =>
        bad := bad + 1
        log <| Json.mkObj [("n", toJson n.toString),("status","FAIL"),("error", toJson ((← e.toMessageData.toString).take 1500).toString)]
    for n in copied do
      if let some (.thmInfo _) := env.find? n then
        let ax ← collectAxioms (ren n)
        log <| Json.mkObj [("axioms", toJson (ren n).toString), ("value", toJson (ax.map toString))]
    if let some ci := (← getEnv).find? `NPP_Nov.AspisR1.NPN_RecordedHost.runs_of_residual then
      log <| Json.mkObj [("runs_of_residual_type", toJson (← ppExpr ci.type).pretty)]
    return if bad == 0 then 0 else 3
  let (code, st') ← (act.run' {} {}).toIO ctx st
  if code != 0 then return code
  writeModule st'.env s!"{outDir}/NPP_RecordedHostNov.olean" (writeIR := false)
  log <| Json.mkObj [("event","written"),("module","NPP_RecordedHostNov")]
  return 0
end NPP_Repoint

def main (args : List String) : IO UInt32 := NPP_Repoint.run (args.headD "out")
