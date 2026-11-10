import Lean
/-! NPO_ kernel-checked re-instantiation ("clone") of the run-7 cone at other program ids.
Usage: NPO_Clone <Inst> <OutModule> [orig=replacement ...]
 Inst = Nov | Oct. The three id constants
   AspisR1.CPH_Program.verifier, NHJ_IdPacket.poolDefault, NHJ_IdPacket.registryDefault
 are replaced by NPO_DeployedIds.{verifier,pool,registry}<Inst>. Every constant reachable from
 the run-7 roots that depends on them (type, value, or a projection's structure) is copied under
 the prefix NPO_<Inst> with every reference renamed, and each copy is sent to the kernel with
 Kernel.Environment.addDeclCore (full type checking; no addDeclWithoutChecking anywhere).
 Optional orig=replacement pairs map a dependent to a hand-written restatement instead of a copy.
 On full success the new constants are written as <OutModule>.olean (imports TAS_FinalB,
 NPO_DeployedIds and any extra modules named by --import=M). -/
open Lean
namespace NPO_Clone
def roots : Array Name := #[`AspisR1.TAS_FinalB.deployed_splitB, `AspisR1.TAS_FinalB.deployed_charge,
  `AspisR1.TAS_FinalB.fail_sub_rec, `AspisR1.NNH8_DeployedOuter]

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
@[implemented_by usedImpl] opaque used (es : List Expr) : NameSet

def depsOf (env : Environment) (ci : ConstantInfo) : NameSet :=
  match ci with
  | .inductInfo ii =>
    let ctorTys := ii.all.flatMap fun i => match env.find? i with
      | some (.inductInfo jj) => jj.ctors.filterMap fun c => (env.find? c).map (·.type)
      | _ => []
    let tys := ii.all.filterMap fun i => (env.find? i).map (·.type)
    (used (tys ++ ctorTys)).filter fun n => !(ii.all.contains n) && !(ii.ctors.contains n)
  | .ctorInfo c => (used [c.type]).insert c.induct
  | _ => match ci.value? (allowOpaque := true) with
    | some v => used [ci.type, v]
    | none => used [ci.type]

partial def substE (isDep : Name → Bool) (ren : Name → Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n us => if isDep n then some (.const (ren n) us) else none
    | .proj s i b => if isDep s then some (.proj (ren s) i (substE isDep ren b)) else none
    | _ => none

def kind : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .inductInfo _ => "induct" | .quotInfo _ => "quot"

def log (j : Json) : IO Unit := do IO.println j.compress; (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let inst := args[0]!
  let outMod := args[1]!.toName
  let extra := (args.drop 2).filter (·.startsWith "--import=") |>.map (·.drop 9 |>.toString.toName)
  let outDir := ((args.drop 2).find? (·.startsWith "--out=")).map (·.drop 6 |>.toString) |>.getD "out"
  let pairs := (args.drop 2).filter (fun a => !a.startsWith "--") |>.map fun a =>
    match a.splitOn "=" with | [o, r] => (o.toName, r.toName) | _ => panic! a
  let pre := Name.mkSimple s!"NPO_{inst}"
  let targetMap : Std.HashMap Name Name := Std.HashMap.ofList [
    (`AspisR1.CPH_Program.verifier, Name.mkStr `NPO_DeployedIds s!"verifier{inst}"),
    (`NHJ_IdPacket.poolDefault, Name.mkStr `NPO_DeployedIds s!"pool{inst}"),
    (`NHJ_IdPacket.registryDefault, Name.mkStr `NPO_DeployedIds s!"registry{inst}")]
  let imports := #[`TAS_FinalB, `NPO_DeployedIds] ++ extra.toArray
  let env ← importModules (imports.map fun m => {module := m}) {} (trustLevel := 1024) (loadExts := false)
  -- 1. dependency walk (post-order), dependents = depend on a target
  let mut dep : Std.HashMap Name Bool := {}
  let mut started : Std.HashSet Name := {}
  let mut order : Array Name := #[]
  let mut stack : Array (Name × Bool) := roots.map (·, false)
  while h : stack.size > 0 do
    let (n, ex) := stack.back
    stack := stack.pop
    if dep.contains n then continue
    match env.find? n with
    | none => dep := dep.insert n false
    | some ci =>
      let ds := depsOf env ci
      if !ex then
        if started.contains n then continue
        started := started.insert n
        stack := stack.push (n, true)
        for d in ds do
          if !dep.contains d then stack := stack.push (d, false)
      else
        let b := targetMap.contains n || ds.any (fun d => dep.getD d false)
        dep := dep.insert n b
        if b && !targetMap.contains n then order := order.push n
  log <| Json.mkObj [("event","walk"),("reachable", toJson dep.size),("dependents", toJson order.size)]
  let override : Std.HashMap Name Name := Std.HashMap.ofList pairs
  let ren (n : Name) : Name :=
    match targetMap[n]? with
    | some m => m
    | none => match override[n]? with
      | some m => m
      | none => if dep.getD n false then pre ++ n else n
  let subP := substE (fun n => dep.getD n false) ren
  let cv (c : ConstantVal) : ConstantVal := { c with name := ren c.name, type := subP c.type }
  -- 2. add clones in post-order
  let mut kenv := env.toKernelEnv
  let mut bad : Std.HashSet Name := {}
  let mut nOk := 0
  for n in order do
    if override.contains n then continue
    let some ci := env.find? n | continue
    let ds := depsOf env ci
    if let some b := ds.toList.find? (fun d => bad.contains d) then
      bad := bad.insert n
      log <| Json.mkObj [("n", toJson n.toString),("k", kind ci),("status","blocked"),("by", toJson b.toString)]
      continue
    let decl? : Option Declaration := match ci with
      | .defnInfo v => some <| .defnDecl { v with toConstantVal := cv v.toConstantVal, value := subP v.value, all := v.all.map ren }
      | .thmInfo v => some <| .thmDecl { v with toConstantVal := cv v.toConstantVal, value := subP v.value, all := v.all.map ren }
      | .opaqueInfo v => some <| .opaqueDecl { v with toConstantVal := cv v.toConstantVal, value := subP v.value, all := v.all.map ren }
      | .inductInfo v =>
        let mkCtor (c : Name) : Option Constructor :=
          (env.find? c).map (fun cc => { name := ren c, type := subP cc.type })
        let mkType (i : Name) : Option InductiveType :=
          match env.find? i with
          | some (.inductInfo w) => some { name := ren w.name, type := subP w.type, ctors := w.ctors.filterMap mkCtor }
          | _ => none
        let types := v.all.filterMap mkType
        if v.all.head? == some n then some (.inductDecl v.levelParams v.numParams types v.isUnsafe) else none
      | _ => none
    match decl? with
    | none =>
      -- constructors / recursors / non-head mutual members: generated by the inductive; compare below
      match ci with
      | .ctorInfo c =>
        match kenv.find? (ren n) with
        | some (.ctorInfo c') =>
          let ok := c'.type == subP c.type && c'.cidx == c.cidx && c'.numFields == c.numFields && c'.induct == ren c.induct
          if !ok then bad := bad.insert n
          log <| Json.mkObj [("n", toJson n.toString),("k","ctor"),("status", if ok then "ok-generated" else "mismatch")]
        | _ => bad := bad.insert n; log <| Json.mkObj [("n", toJson n.toString),("k","ctor"),("status","missing")]
      | _ => log <| Json.mkObj [("n", toJson n.toString),("k", kind ci),("status","skipped")]
    | some d =>
      let t0 ← IO.monoMsNow
      match kenv.addDeclCore 0 d none with
      | .ok k =>
        kenv := k; nOk := nOk + 1
        log <| Json.mkObj [("n", toJson n.toString),("k", kind ci),("status","ok"),("ms", toJson ((← IO.monoMsNow) - t0)),
          ("type_changed", toJson (subP ci.type != ci.type))]
      | .error ex =>
        bad := bad.insert n
        let msg ← (ex.toMessageData {}).toString
        log <| Json.mkObj [("n", toJson n.toString),("k", kind ci),("status","FAIL"),("ms", toJson ((← IO.monoMsNow) - t0)),
          ("error", toJson (msg.take 1500).toString)]
  log <| Json.mkObj [("event","done"),("added", toJson nOk),("failed_or_blocked", toJson bad.size)]
  if bad.size > 0 then return 2
  let env' := (Environment.ofKernelEnv kenv).setMainModule outMod
  writeModule env' s!"{outDir}/{outMod}.olean" (writeIR := false)
  log <| Json.mkObj [("event","written"),("module", toJson outMod.toString)]
  return 0
end NPO_Clone
def main (args : List String) : IO UInt32 := NPO_Clone.main args
