import Lean
open Lean
/-- The function boundary drops every ModuleData reference before the caller frees regions. -/
unsafe def inspect (p : System.FilePath) (known : Option (Std.HashSet String)) :
    IO (String × Array CompactedRegion) := do
 let mut files := #[p]
 for suffix in ["server", "private"] do
  let q := p.addExtension suffix
  if ← q.pathExists then files := files.push q
 let parts ← readModuleDataParts files
 let mut names : Array String := #[]
 let mut imports : Array String := #[]
 let mut dangling : Array Json := #[]
 let mut count := 0
 let mut edges := 0
 for (data, _) in parts do
  for i in data.imports do
   if !imports.contains i.module.toString then imports := imports.push i.module.toString
  for c in data.constants do
   count := count + 1
   if known.isNone then names := names.push c.name.toString
   if let some set := known then
    let mut refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
    if let .inductInfo v := c then refs := refs ++ v.ctors.toArray
    for dep in refs do
     edges := edges + 1
     if !set.contains dep.toString then
      dangling := dangling.push (Json.mkObj [("parent", toJson c.name.toString), ("missing", toJson dep.toString)])
 let encoded := (Json.mkObj [("path", toJson p.toString), ("imports", toJson imports),
   ("names", toJson names), ("declarations", toJson count), ("edges", toJson edges),
   ("dangling", toJson dangling)]).compress
 return (encoded, parts.map Prod.snd)
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
   let p ← locate n
   let (encoded, regions) ← inspect p none
   for region in regions.reverse do region.free
   let row ← IO.ofExcept (Json.parse encoded)
   let imports ← IO.ofExcept (row.getObjValAs? (Array String) "imports")
   out.putStrLn (← IO.ofExcept (row.setObjVal? "module" (toJson n))).compress
   out.flush
   for i in imports do pending := pending.push i
 else
  let knownText ← IO.FS.readFile (System.FilePath.mk args[3]!)
  let known : Std.HashSet String := (knownText.splitOn "\n").foldl (fun s n => s.insert n) {}
  let manifest ← IO.FS.lines (System.FilePath.mk args[4]!)
  for line in manifest do
   let row ← IO.ofExcept (Json.parse line)
   let n ← IO.ofExcept (row.getObjValAs? String "module")
   let expected ← IO.ofExcept (row.getObjValAs? (Array String) "imports")
   let p ← locate n
   let (encoded, regions) ← inspect p (some known)
   for region in regions.reverse do region.free
   let result ← IO.ofExcept (Json.parse encoded)
   let imports ← IO.ofExcept (result.getObjValAs? (Array String) "imports")
   let result ← IO.ofExcept (result.setObjVal? "module" (toJson n))
   let result ← IO.ofExcept (result.setObjVal? "imports_match" (toJson (imports == expected)))
   out.putStrLn result.compress
   out.flush
 return 0
