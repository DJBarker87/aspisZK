import Lean
open Lean
/-- Remove binder labels and metadata only. Bound indices, constants, literals,
universe levels, binder kinds and all type/application structure are retained. -/
private def alpha (e : Expr) : Expr :=
  match e with
  | .app f a => .app (alpha f) (alpha a)
  | .lam _ t b k => .lam .anonymous (alpha t) (alpha b) k
  | .forallE _ t b k => .forallE .anonymous (alpha t) (alpha b) k
  | .letE _ t v b n => .letE .anonymous (alpha t) (alpha v) (alpha b) n
  | .mdata _ b => alpha b
  | .proj n i b => .proj n i (alpha b)
  | _ => e
private unsafe def load (path root expected : String) : IO (Option ConstantInfo × Array CompactedRegion) := do
  let p : System.FilePath := path
  let mut parts := #[p]
  let privatePart : System.FilePath := path ++ ".private"
  if ← privatePart.pathExists then parts := parts.push privatePart
  let data ← readModuleDataParts parts
  let mut found := none
  for (d, _) in data do
    for info in d.constants do
      if info.name.toString == root && reprStr info.type == expected then found := some info
  return (found, data.map Prod.snd)
/-- Check captured source/merged type pairs without importing their combined environments. -/
unsafe def main (args : List String) : IO UInt32 := do
  let .ok j := Json.parse (← IO.FS.readFile args[0]!) | return 2
  let .ok pairs := fromJson? (α := Array Json) j | return 2
  let mut failed := false
  for pair in pairs do
    let .ok root := pair.getObjValAs? String "root" | return 2
    let .ok sourceType := pair.getObjValAs? String "source_type" | return 2
    let .ok mergedType := pair.getObjValAs? String "merged_type" | return 2
    let .ok sourcePaths := pair.getObjValAs? (Array String) "source_paths" | return 2
    let .ok mergedPath := pair.getObjValAs? String "merged_path" | return 2
    let mut sourceInfo := none
    let mut regions : Array CompactedRegion := #[]
    for path in sourcePaths do
      let (info, rs) ← load path root sourceType
      regions := regions ++ rs
      if info.isSome then sourceInfo := info
    let (mergedInfo, rs) ← load mergedPath root mergedType
    regions := regions ++ rs
    let some old := sourceInfo | IO.eprintln ("missing source type " ++ root); return 2
    let some current := mergedInfo | IO.eprintln ("missing merged type " ++ root); return 2
    let levelsEqual := old.levelParams == current.levelParams
    let rawEqual := old.type == current.type
    let alphaEqual := alpha old.type == alpha current.type
    let equal := levelsEqual && alphaEqual
    IO.println ((Json.mkObj [("root", toJson root), ("same_levels", toJson levelsEqual),
      ("expr_equal", toJson rawEqual), ("annotation_only_equal", toJson alphaEqual),
      ("compatible", toJson equal), ("retained_regions", toJson regions.size)]).compress)
    unless equal do failed := true
  return if failed then 1 else 0
#print axioms main
