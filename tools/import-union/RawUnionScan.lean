import Lean
open Lean
private def declarationKind : ConstantInfo → String
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def readComplete (p : System.FilePath) : IO (ModuleData × ModuleData) := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let companion : System.FilePath := p.toString ++ suffix
    if ← companion.pathExists then files := files.push companion
  let parts ← readModuleDataParts files
  let some (header, _) := parts.toList.head? | throw (IO.userError "Empty module parts")
  let some (full, _) := parts.toList.getLast? | throw (IO.userError "Empty module parts")
  pure (header, full)

#eval show IO Unit from do
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let outputPath := "evidence/raw-union.jsonl"
  let out ← IO.FS.Handle.mk outputPath .write
  let mut pending := ["ImportUnionReleaseGate"]
  let mut visited : List String := []
  let mut objects : Array (String × System.FilePath) := #[]
  let mut names : Std.HashMap Name (Array (String × String)) := {}
  while !pending.isEmpty do
    let owner := pending.head!
    pending := pending.tail!
    if visited.contains owner then continue
    visited := owner :: visited
    let mut found : Option System.FilePath := none
    for root in roots do
      let p : System.FilePath := root ++ "/" ++ owner.replace "." "/" ++ ".olean"
      if ← p.pathExists then
        found := some p
        break
    let some p := found | throw (IO.userError s!"Missing object {owner}")
    let (header, data) ← readComplete p
    objects := objects.push (owner, p)
    let imports := header.imports.map (fun i => i.module.toString)
    out.putStrLn ("RAW_MODULE " ++ (Json.arr #[toJson owner, toJson p.toString, toJson imports]).compress)
    for ci in data.constants do
      let kind := declarationKind ci
      names := names.insert ci.name ((names[ci.name]?.getD #[]).push (owner, kind))
      out.putStrLn ("RAW_DECL " ++ (Json.arr #[toJson ci.name.toString, toJson owner, toJson kind]).compress)
      if ["AspisR1.SpendRelation.Rspend", "AspisR1.SpendRelation.check"].contains ci.name.toString then
        if let some value := ci.value? then
          out.putStrLn ("RAW_SEMANTIC_DEF " ++ (Json.arr #[toJson ci.name.toString,
            toJson owner, toJson ((hash value).toNat),
            toJson (value.getUsedConstants.map Name.toString)]).compress)
    pending := imports.toList ++ pending
    out.flush
    IO.FS.writeFile "evidence/raw-scan-progress.json" ("modules " ++ toString visited.length ++ " last " ++ owner)
  -- Compare duplicate types exactly as expressions; compacted regions remain
  -- allocated until process exit. Persist only hashes, avoiding expansion of
  -- shared expression DAGs into unbounded textual trees.
  let mut types : Std.HashMap Name Expr := {}
  let mut equal : Std.HashMap Name Bool := {}
  for (owner, p) in objects do
    let (_, data) ← readComplete p
    for ci in data.constants do
      if (names[ci.name]?.getD #[]).size > 1 then
        let typeHash := (hash ci.type).toNat
        if let some old := types[ci.name]? then
          equal := equal.insert ci.name ((equal[ci.name]?.getD true) && old == ci.type)
        else
          types := types.insert ci.name ci.type
        out.putStrLn ("RAW_DUP_TYPE " ++ (Json.arr #[toJson ci.name.toString, toJson owner, toJson typeHash]).compress)
  for (name, owners) in names.toArray do
    if owners.size > 1 then
      let kinds := owners.map Prod.snd
      let sameType := equal[name]?.getD true
      let allowed := kinds.all (· == "theorem") && sameType
      out.putStrLn ("RAW_DUP " ++ (Json.arr #[toJson name.toString, toJson owners, toJson sameType, toJson allowed]).compress)

  out.flush
  IO.println ("RAW_SCAN_FILE " ++ outputPath ++ " modules=" ++ toString objects.size)
