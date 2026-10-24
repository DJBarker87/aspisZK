import Lean
open Lean
namespace Port29SDKDATA
-- Exact accepted Port18 helpers; readComplete is retained for copy assessment,
-- but streaming calls below own/free the complete region stack explicitly.
def sameDeclaration (a b : ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .quotInfo a, .quotInfo b => a.toConstantVal == b.toConstantVal &&
      match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | .inductInfo a, .inductInfo b =>
      a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec &&
      a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => false
def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty module")
  pure data

private def owned (s : String) : String := String.ofList s.toList
private def ns (n : Name) : String := owned n.toString
private def emit (h : IO.FS.Handle) (j : Json) : IO Unit := h.putStrLn j.compress
private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
private def deps (c : ConstantInfo) : Array String := Id.run do
  let mut ds := c.type.getUsedConstants
  if let some v := c.value? (allowOpaque := true) then ds := ds ++ v.getUsedConstants
  match c with
  | .inductInfo v =>
    ds := ds ++ v.all.toArray ++ v.ctors.toArray
    for n in v.all do ds := ds.push (n.str "rec")
  | .defnInfo v => ds := ds ++ v.all.toArray
  | .thmInfo v => ds := ds ++ v.all.toArray
  | .opaqueInfo v => ds := ds ++ v.all.toArray
  | .ctorInfo v => ds := ds.push v.induct
  | .recInfo v =>
    ds := ds ++ v.all.toArray
    for n in v.all do ds := ds.push (n.str "rec")
    for r in v.rules do ds := (ds.push r.ctor) ++ r.rhs.getUsedConstants
  | _ => pure ()
  let mut out : Std.HashSet String := {}
  for n in ds do out := out.insert (ns n)
  return out.toArray
private def metadata (c : ConstantInfo) : Json :=
  match c with
  | .defnInfo v => toJson (v.all.toArray.map ns, toString (repr v.safety))
  | .thmInfo v => toJson (v.all.toArray.map ns)
  | .opaqueInfo v => toJson (v.all.toArray.map ns)
  | .inductInfo v => Json.arr #[toJson (v.all.toArray.map ns),toJson (v.ctors.toArray.map ns),
      toJson v.numParams,toJson v.numIndices,toJson v.numNested,toJson v.isRec,toJson v.isReflexive]
  | .ctorInfo v => toJson (ns v.induct,v.cidx,v.numParams,v.numFields)
  | .recInfo v => Json.arr #[toJson (v.all.toArray.map ns),toJson v.numParams,toJson v.numIndices,
      toJson v.numMotives,toJson v.numMinors,toJson v.k,
      toJson (v.rules.toArray.map (fun r => (ns r.ctor,r.nfields,r.rhs.getUsedConstants.map ns)))]
  | _ => Json.null
private def record (c : ConstantInfo) : Json := Json.mkObj [
  ("name",toJson (ns c.name)),("kind",toJson (kind c)),
  ("levels",toJson (c.levelParams.toArray.map ns)),("unsafe",toJson c.isUnsafe),
  ("partial",toJson c.isPartial),("has_value",toJson (c.hasValue (allowOpaque := true))),
  ("metadata",metadata c),("dependencies",toJson (deps c))]
private def readParts (p : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let mut ps := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then ps := ps.push q
  readModuleDataParts ps
private unsafe def indexOne (h : IO.FS.Handle) (side origin m p : String) : IO Unit := do
  let loaded ← readParts p
  let mut i := 0
  for (data,_) in loaded do
    emit h (Json.mkObj [("tag",toJson "part"),("side",toJson side),("origin",toJson origin),
      ("module",toJson m),("path",toJson p),("part",toJson i),
      ("constants",toJson data.constants.size),("names",toJson data.constNames.size),
      ("consistent",toJson (data.constNames == data.constants.map (·.name))),
      ("imports",toJson (data.imports.map (fun x => ns x.module))),
      ("extra",toJson data.extraConstNames.size),("entries",toJson data.entries.size)])
    for c in data.constants do
      emit h (Json.mkObj [("tag",toJson "constant"),("side",toJson side),("origin",toJson origin),
        ("module",toJson m),("path",toJson p),("part",toJson i),("constant",record c)])
    i := i + 1
  (loaded.map (·.2)).reverse.forM CompactedRegion.free
private def rawCheck (d : ModuleData) : IO Unit := do
  unless d.imports.isEmpty && d.extraConstNames.isEmpty && d.entries.isEmpty &&
      d.constNames == d.constants.map (·.name) do
    throw (IO.userError "invalid raw transport header")
private unsafe def compareOne (h : IO.FS.Handle) (tag p q : String) (names : Array String) : IO Unit := do
  let a ← readParts p
  let b ← readParts q
  let some (da,_) := a.toList.getLast? | throw (IO.userError "empty left")
  let some (db,_) := b.toList.getLast? | throw (IO.userError "empty right")
  -- Original object comparisons are allowed only for incremental counterpart work.
  if tag != "full-original-current" then rawCheck da
  rawCheck db
  for n in names do
    let ca := da.constants.find? (fun c => ns c.name == n)
    let cb := db.constants.find? (fun c => ns c.name == n)
    match ca,cb with
    | some x,some y =>
      let same := sameDeclaration x y
      let proofOnly := match x,y with
        | .thmInfo v,.thmInfo w => v.toConstantVal == w.toConstantVal && v.all == w.all
        | _,_ => false
      emit h (Json.mkObj [("tag",toJson tag),("name",toJson n),("left",toJson p),("right",toJson q),
        ("sameDeclaration",toJson same),("same_constant_val",toJson (x.toConstantVal == y.toConstantVal)),
        ("same_value",toJson (x.value? (allowOpaque := true) == y.value? (allowOpaque := true))),
        ("proof_only_same_full_type",toJson (!same && proofOnly)),
        ("left_info",record x),("right_info",record y)])
    | _,_ => emit h (Json.mkObj [("tag",toJson tag),("name",toJson n),("left",toJson p),("right",toJson q),
        ("missing_left",toJson ca.isNone),("missing_right",toJson cb.isNone)])
  (b.map (·.2)).reverse.forM CompactedRegion.free
  (a.map (·.2)).reverse.forM CompactedRegion.free
private unsafe def exportOne (h : IO.FS.Handle) (side origin m p dest : String) (names : Array String) : IO Unit := do
  let loaded ← readParts p
  let mut wanted : Std.HashSet String := {}
  for n in names do wanted := wanted.insert n
  let mut i := 0
  for (data,_) in loaded do
    let cs := data.constants.filter (fun c => wanted.contains (ns c.name))
    unless cs.isEmpty do
      let path : System.FilePath := dest ++ "-part-" ++ toString i ++ ".olean"
      IO.FS.createDirAll path.parent.get!
      saveModuleData path m.toName { data with
        imports := #[]
        constants := cs
        constNames := cs.map (·.name)
        extraConstNames := #[]
        entries := #[] }
      -- New output audit, within the SAME diagnostic invocation: raw read only.
      let (check,region) ← readModuleData path
      rawCheck check
      unless check.constants.size == cs.size do throw (IO.userError "export count mismatch")
      for c in check.constants do
        let some original := cs.find? (fun x => x.name == c.name)
          | throw (IO.userError "export unexpected name")
        unless sameDeclaration original c do throw (IO.userError "export declaration mismatch")
      region.free
      emit h (Json.mkObj [("tag",toJson "transport"),("side",toJson side),("origin",toJson origin),
        ("module",toJson m),("source",toJson p),("path",toJson path.toString),("part",toJson i),
        ("names",toJson (cs.map (fun c => ns c.name)))])
    i := i + 1
  (loaded.map (·.2)).reverse.forM CompactedRegion.free
private unsafe def main : IO Unit := do
  let some dir ← IO.getEnv "PORT29_DATA" | throw (IO.userError "PORT29_DATA")
  let h ← IO.FS.Handle.mk (dir ++ "/Port29SDKDATA_raw.jsonl") .write
  for row in ← IO.FS.lines (dir ++ "/Port29SDKDATA_index.tsv") do
    if row.isEmpty then continue
    let [side,origin,m,p] := row.splitOn "\t" | throw (IO.userError "index row")
    indexOne h side origin m p
  for row in ← IO.FS.lines (dir ++ "/Port29SDKDATA_compare.tsv") do
    if row.isEmpty then continue
    let tag::p::q::names := row.splitOn "\t" | throw (IO.userError "compare row")
    compareOne h tag p q names.toArray
  h.flush
  if (← IO.getEnv "PORT29_INTERACTIVE") == some "1" then
    IO.FS.writeFile (dir ++ "/Port29SDKDATA_index-ready") "ready\n"
    let ready : System.FilePath := dir ++ "/Port29SDKDATA_export-ready"
    while !(← ready.pathExists) do IO.sleep 100
    for row in ← IO.FS.lines (dir ++ "/Port29SDKDATA_extra-compare.tsv") do
      if row.isEmpty then continue
      let tag::p::q::names := row.splitOn "\t" | throw (IO.userError "extra compare row")
      compareOne h tag p q names.toArray
  for row in ← IO.FS.lines (dir ++ "/Port29SDKDATA_export.tsv") do
    if row.isEmpty then continue
    let side::origin::m::p::dest::names := row.splitOn "\t" | throw (IO.userError "export row")
    exportOne h side origin m p dest names.toArray
  h.flush
  IO.println "Port29SDKDATA raw diagnostic finished; axioms=N/A; no kernel insertion"
end Port29SDKDATA
#eval Port29SDKDATA.main
