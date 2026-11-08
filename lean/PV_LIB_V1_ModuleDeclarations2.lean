import Lean
open Lean
/-- Inspect retained module headers without loading their combined environments. -/
unsafe def main (args : List String) : IO UInt32 := do
  let .ok j := Json.parse (← IO.FS.readFile args[0]!) | return 2
  let .ok paths := fromJson? (α := Array String) j | return 2
  for path in paths do
    let p : System.FilePath := path
    let mut parts := #[p]
    let privatePart : System.FilePath := path ++ ".private"
    if ← privatePart.pathExists then parts := parts.push privatePart
    let data ← readModuleDataParts parts
    let names := data.flatMap fun (d, _) => d.constNames ++ d.extraConstNames
    let some (first, _) := data[0]? | return 2
    let imports := first.imports.map fun i => i.module.toString
    IO.println ((Json.mkObj [("path", toJson path), ("imports", toJson imports),
      ("declarations", toJson (names.map Name.toString))]).compress)
  return 0
#print axioms main
