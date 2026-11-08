import Lean
open Lean
private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
private def body : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none
/-- Check repeated actual kernel names without constructing the combined environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  let .ok j := Json.parse (← IO.FS.readFile args[0]!) | return 2
  let .ok paths := j.getObjValAs? (Array String) "paths" | return 2
  let .ok names := j.getObjValAs? (Array String) "names" | return 2
  let wanted : Std.HashSet String := names.foldl (fun s n => s.insert n) {}
  let mut seen : Std.HashMap Name (String × ConstantInfo × Bool) := {}
  let mut regions : Array CompactedRegion := #[]
  let mut failed := false
  let mut compared := 0
  let mut publicDuplicates := 0
  for path in paths do
    let p : System.FilePath := path
    let mut parts := #[p]
    let privatePart : System.FilePath := path ++ ".private"
    if ← privatePart.pathExists then parts := parts.push privatePart
    let data ← readModuleDataParts parts
    let mut own : Std.HashMap Name (ConstantInfo × Bool) := {}
    for ((d, _), index) in data.toList.zipIdx do
      for info in d.constants do
        if wanted.contains info.name.toString then
          let wasPublic := (own[info.name]?).any (fun x => x.2)
          own := own.insert info.name (info, wasPublic || index == 0)
    if !own.isEmpty then
      regions := regions ++ data.map Prod.snd
    for (name, info, isPublic) in own.toList.map (fun (n, (i, p)) => (n, i, p)) do
      match seen[name]? with
      | none => seen := seen.insert name (path, info, isPublic)
      | some (previous, old, wasPublic) =>
        let typeEqual := old.type == info.type
        let kindEqual := kind old == kind info
        let valueEqual := body old == body info
        let supported := kind info == "theorem" || kind info == "def" || kind info == "opaque"
        let equal := typeEqual && kindEqual && valueEqual && supported
        compared := compared + 1
        if isPublic && wasPublic then publicDuplicates := publicDuplicates + 1
        IO.println ((Json.mkObj [("name", toJson name.toString),
          ("previous", toJson previous), ("current", toJson path),
          ("kind", toJson (kind info)), ("same_type", toJson typeEqual),
          ("same_definition", toJson valueEqual), ("supported", toJson supported),
          ("both_public", toJson (isPublic && wasPublic)), ("compatible", toJson equal)]).compress)
        unless equal do failed := true
  IO.println ((Json.mkObj [("comparisons", toJson compared),
    ("public_duplicates", toJson publicDuplicates), ("compatible", toJson (!failed)),
    ("retained_regions", toJson regions.size)]).compress)
  return if failed then 1 else 0
#print axioms main
