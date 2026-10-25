import Lean
open Lean
-- Untrusted raw-data diagnostic. No original module is imported or checked.
private def owned (s : String) : String := String.ofList s.toList
private def ns (n : Name) : String := owned n.toString
private def emit (tag : String) (j : Json) : IO Unit := IO.println (tag ++ " " ++ j.compress)
private def readParts (p : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let mut ps := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then ps := ps.push q
  readModuleDataParts ps
private def deps (c : ConstantInfo) : Array Name := Id.run do
  let mut ds := c.type.getUsedConstants
  if let some v := c.value? (allowOpaque := true) then ds := ds ++ v.getUsedConstants
  match c with
  | .inductInfo v =>
    ds := ds ++ v.all.toArray ++ v.ctors.toArray
    for n in v.all do ds := ds.push (n.str "rec")
  | .ctorInfo v => ds := ds.push v.induct
  | .recInfo v =>
    ds := ds ++ v.all.toArray
    for n in v.all do ds := ds.push (n.str "rec")
    for r in v.rules do ds := (ds.push r.ctor) ++ r.rhs.getUsedConstants
  | _ => pure ()
  return ds
private def family (roots : Array Name) (c : ConstantInfo) : Bool :=
  roots.any (fun n => n.isPrefixOf (privateToUserName c.name))
private def select (origin m dest : String) (data : ModuleData)
    (seeds : Array Name) (needed : Std.HashSet String) : IO (Std.HashSet String × Array String) := do
  let mut needed := needed
  let mut selected : Std.HashSet String := {}
  let mut groups := seeds
  let mut progress := true
  while progress do
    progress := false
    for c in data.constants do
      let n := ns c.name
      if !selected.contains n && (needed.contains n || family groups c) then
        selected := selected.insert n
        needed := needed.insert n
        progress := true
        if let .inductInfo v := c then groups := groups ++ v.all.toArray
        let ds := (deps c).map ns
        match c with
        | .inductInfo v => emit "GROUP" (toJson (origin,n,"inductive",v.all.toArray.map ns,v.ctors.toArray.map ns))
        | .ctorInfo v => emit "GROUP" (toJson (origin,n,"constructor",#[ns v.induct],(#[] : Array String)))
        | .recInfo v => emit "GROUP" (toJson (origin,n,"recursor",v.all.toArray.map ns,v.rules.toArray.map (fun r => ns r.ctor)))
        | _ => pure ()
        for d in ds do needed := needed.insert d
        emit "EDGE" (toJson (origin,m,n,ds))
  let cs := data.constants.filter (fun c => selected.contains (ns c.name))
  unless cs.isEmpty do
    let p : System.FilePath := dest
    IO.FS.createDirAll p.parent.get!
    -- Full original ConstantInfo values/metadata, only transport fields cleared.
    saveModuleData p m.toName { data with imports := #[], constants := cs,
      constNames := cs.map (·.name), extraConstNames := #[], entries := #[] }
    emit "TRANSPORT" (toJson (origin,m,dest,cs.map (fun c => ns c.name)))
  -- Only independent strings/sets escape the compacted-region callback.
  return (needed,cs.map (fun c => ns c.name))
private unsafe def scan (origin m p dest : String) (seeds : Array Name)
    (needed : Std.HashSet String) : IO (Std.HashSet String × Array String) := do
  let loaded ← readParts p
  let some (data,_) := loaded.toList.getLast? | throw (IO.userError "empty parts")
  emit "HEADER" (toJson (origin,m,data.imports.map (fun i => ns i.module)))
  let result ← select origin m dest data seeds needed
  -- Force ownership-sensitive work before releasing regions, as in Port18.
  let size := result.2.foldl (fun k s => k+s.length) 0
  if size > 100000000 then throw (IO.userError "name bound")
  (loaded.map (·.2)).reverse.forM CompactedRegion.free
  return result
private unsafe def coreNames (p : String) (needed : Std.HashSet String) : IO (Array String) := do
  let (data,region) ← readModuleData p
  let names := data.constNames.filterMap (fun n => if needed.contains (ns n) then some (ns n) else none)
  let size := names.foldl (fun k s => k+s.length) 0
  if size > 100000000 then throw (IO.userError "name bound")
  region.free
  return names
private unsafe def Port28ROOTEXPORT_main : IO Unit := do
  let some dir ← IO.getEnv "PORT28_DATA" | throw (IO.userError "PORT28_DATA")
  let rows := (← IO.FS.lines (dir ++ "/objects.tsv")).filter (· != "")
  let seedRows := (← IO.FS.lines (dir ++ "/seeds.tsv")).filter (· != "")
  let mut needed : Std.HashSet String := {}
  for row in seedRows do
    let fields := row.splitOn "\t"
    if let [_,n] := fields then needed := needed.insert n
    else throw (IO.userError "seed row")
  let mut done : Std.HashSet String := {}
  let mut round := 0
  let mut previous := 0
  repeat
    previous := needed.size
    round := round+1
    for row in rows do
      let [origin,m,p] := row.splitOn "\t" | throw (IO.userError "object row")
      let seeds := seedRows.filterMap (fun r => match r.splitOn "\t" with
        | [mod,n] => if mod == m then some n.toName else none
        | _ => none)
      let dest := dir ++ "/transports/round-" ++ toString round ++ "/" ++ origin ++ "/" ++ m.replace "." "/" ++ ".olean"
      let (next,names) ← scan origin m p dest seeds needed
      needed := next
      for n in names do done := done.insert n
    emit "ROUND" (toJson (round,needed.size,done.size))
    if needed.size == previous then break
  let mut unresolved := needed.toArray.filter (fun n => !done.contains n)
  let mut core : Std.HashSet String := {}
  for p in ← IO.FS.lines (dir ++ "/core.tsv") do
    for n in ← coreNames p needed do
      if !done.contains n then
        core := core.insert n
        emit "CORE_LEAF" (toJson (n,p))
  unresolved := unresolved.filter (fun n => !core.contains n)
  emit "UNRESOLVED" (toJson unresolved)
  emit "SUMMARY" (toJson (round,needed.size,done.size,core.size,unresolved.size))
#eval Port28ROOTEXPORT_main
