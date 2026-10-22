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

#eval show IO Unit from do
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let excluded := ["Init", "Lean", "Std", "Mathlib", "Batteries", "Aeneas", "AeneasMeta",
    "Aesop", "Qq", "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Lake"]
  let mut pending := ["ImportUnionReleaseGate"]
  let mut visited : List String := []
  let mut objects : Array (String × System.FilePath) := #[]
  let mut names : Std.HashMap Name (Array (String × String)) := {}
  while !pending.isEmpty do
    let owner := pending.head!
    pending := pending.tail!
    if visited.contains owner || excluded.contains (owner.splitOn ".").head! then continue
    visited := owner :: visited
    let mut found : Option System.FilePath := none
    for root in roots do
      let p : System.FilePath := root ++ "/" ++ owner.replace "." "/" ++ ".olean"
      if ← p.pathExists then
        found := some p
        break
    let some p := found | throw (IO.userError s!"Missing object {owner}")
    let (data, _region) ← readModuleData p
    objects := objects.push (owner, p)
    let imports := data.imports.map (fun i => i.module.toString)
    IO.println ("RAW_MODULE " ++ (Json.arr #[toJson owner, toJson p.toString, toJson imports]).compress)
    for ci in data.constants do
      let kind := declarationKind ci
      names := names.insert ci.name ((names[ci.name]?.getD #[]).push (owner, kind))
      IO.println ("RAW_DECL " ++ (Json.arr #[toJson ci.name.toString, toJson owner, toJson kind]).compress)
    pending := imports.toList ++ pending
  -- Read duplicate types separately; retain strings rather than expressions
  -- pointing into compacted object regions after those regions are released.
  let mut types : Std.HashMap Name String := {}
  let mut equal : Std.HashMap Name Bool := {}
  for (owner, p) in objects do
    let (data, _region) ← readModuleData p
    for ci in data.constants do
      if (names[ci.name]?.getD #[]).size > 1 then
        let typeText := reprStr ci.type
        if let some old := types[ci.name]? then
          equal := equal.insert ci.name ((equal[ci.name]?.getD true) && old == typeText)
        else
          types := types.insert ci.name typeText
        IO.println ("RAW_DUP_TYPE " ++ (Json.arr #[toJson ci.name.toString, toJson owner, toJson typeText]).compress)
  for (name, owners) in names.toArray do
    if owners.size > 1 then
      let kinds := owners.map Prod.snd
      let sameType := equal[name]?.getD true
      let allowed := kinds.all (· == "theorem") && sameType
      IO.println ("RAW_DUP " ++ (Json.arr #[toJson name.toString, toJson owners, toJson sameType, toJson allowed]).compress)
