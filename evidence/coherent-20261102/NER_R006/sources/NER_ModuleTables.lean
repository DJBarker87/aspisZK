import Lean
open Lean
/-- Read every private table using Lean's own multi-part reader. Never elaborate proofs. -/
unsafe def tables (p : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
 let mut files := #[p]
 for suffix in ["server", "private"] do
  let q := p.addExtension suffix
  if ← q.pathExists then files := files.push q
 if files.size == 1 then
  let part ← readModuleData p
  return #[part]
 else readModuleDataParts files
unsafe def main (args : List String) : IO UInt32 := do
 let mode := args[0]!
 let dirs := (args[1]!.splitOn ":").map System.FilePath.mk
 let locate := fun (n : String) => do
  let key := n.replace "." "/" ++ ".olean"
  for d in dirs do
   if ← (d / key).pathExists then return d / key
  throw <| IO.userError s!"missing module {n}"
 let out ← IO.FS.Handle.mk (System.FilePath.mk args[2]!) .write
 if mode == "index" then
  let mut pending := (args.drop 3).toArray
  let mut seen : Std.HashSet String := {}
  while !pending.isEmpty do
   let n := pending.back!; pending := pending.pop
   if seen.contains n then continue
   seen := seen.insert n
   IO.eprintln s!"NER_READING {n}"
   let p ← locate n
   IO.eprintln s!"NER_PATH {p}"
   let parts ← tables p
   IO.eprintln s!"NER_LOADED {n}"
   let mut names : Array String := #[]
   let mut imports : Array String := #[]
   for (data, _) in parts do
    for c in data.constants do names := names.push c.name.toString
    for i in data.imports do
     if !imports.contains i.module.toString then imports := imports.push i.module.toString.toList.asString
   let row := Json.mkObj [("module", toJson n), ("path", toJson p.toString),
     ("imports", toJson imports), ("names", toJson names)]
   out.putStrLn row.compress
   out.flush
   for i in imports do pending := pending.push i
   for (_, region) in parts.reverse do region.free
 else
  let knownText ← IO.FS.readFile (System.FilePath.mk args[3]!)
  let known : Std.HashSet String := (knownText.splitOn "\n").foldl (fun s n => s.insert n) {}
  let manifest ← IO.FS.lines (System.FilePath.mk args[4]!)
  for line in manifest do
   let row ← IO.ofExcept (Json.parse line)
   let n ← IO.ofExcept (row.getObjValAs? String "module")
   let expected ← IO.ofExcept (row.getObjValAs? (Array String) "imports")
   let p ← locate n
   let parts ← tables p
   let mut imports : Array String := #[]
   let mut dangling : Array Json := #[]
   let mut count := 0
   let mut edges := 0
   for (data, _) in parts do
    for i in data.imports do
     if !imports.contains i.module.toString then imports := imports.push i.module.toString.toList.asString
    for c in data.constants do
     count := count + 1
     let mut refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
     if let .inductInfo v := c then refs := refs ++ v.ctors.toArray
     for dep in refs do
      edges := edges + 1
      if !known.contains dep.toString then
       dangling := dangling.push (Json.mkObj [("parent", toJson c.name.toString), ("missing", toJson dep.toString)])
   out.putStrLn (Json.mkObj [("module", toJson n), ("path", toJson p.toString),
    ("declarations", toJson count), ("edges", toJson edges),
    ("imports_match", toJson (imports == expected)), ("dangling", toJson dangling)]).compress
   for (_, region) in parts.reverse do region.free
 return 0
