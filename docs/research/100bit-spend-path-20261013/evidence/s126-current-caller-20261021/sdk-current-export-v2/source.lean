import Lean
open Lean
namespace AspisS126SdkCurrentExport
private def clone (s : String) : String := String.ofList s.toList
private def nameString (n : Name) : String := clone n.toString
private def parts (p : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  readModuleDataParts files
private def findObject (roots : List String) (n : String) : IO System.FilePath := do
  for root in roots do
    let p : System.FilePath := root ++ "/" ++ n.replace "." "/" ++ ".olean"
    if ← p.pathExists then return p
  throw (IO.userError s!"Missing object {n}")
private def headerWork (data : ModuleData) : Array String := data.imports.map (fun i => nameString i.module)
private unsafe def readHeader (p : System.FilePath) : IO (Array String) := do
  let (data, region) ← readModuleData p
  let result := headerWork data
  -- Force creation of independent strings before dropping the compacted region.
  let size := result.foldl (fun n s => n+s.length) (0 : Nat)
  if size > 10000000 then throw (IO.userError "unreasonable header")
  region.free
  pure result
private unsafe def visit (roots : List String) (n : String)
    (seen : IO.Ref (Std.HashSet String)) (order : IO.Ref (Array (String × System.FilePath))) : IO Unit := do
  if (← seen.get).contains n then return
  seen.modify (·.insert n)
  let p ← findObject roots n
  for i in ← readHeader p do visit roots i seen order
  order.modify (·.push (n,p))
private def work (m : String) (data : ModuleData) (needed done : Std.HashSet String) :
    IO (Std.HashSet String × Std.HashSet String) := do
  let mut needed := needed
  let mut done := done
  let mut cs : Std.HashMap String ConstantInfo := {}
  for c in data.constants do cs := cs.insert (nameString c.name) c
  let mut pending := cs.toArray.toList.filterMap (fun (n,_) => if needed.contains n then some n else none)
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if done.contains n then continue
    done := done.insert n
    let some c := cs[n]? | throw (IO.userError s!"missing local {n}")
    let mut ds := c.type.getUsedConstants
    if let some v := c.value? (allowOpaque := true) then ds := ds ++ v.getUsedConstants
    if let .inductInfo v := c then
      ds := ds ++ v.ctors.toArray ++ v.all.toArray ++ (v.all.toArray.map (· ++ `rec))
    if let .recInfo v := c then
      ds := ds ++ v.all.toArray
      for rule in v.rules do ds := ds ++ rule.rhs.getUsedConstants
    let names := ds.map nameString
    IO.println ("EDGE " ++ (Json.arr #[toJson m,toJson n,toJson names]).compress)
    for d in names do
      needed := needed.insert d
      if cs.contains d && !done.contains d then pending := d :: pending
  if let some dest ← IO.getEnv "S126_SDK_TRANSPORT" then
    let selected := data.constants.filter (fun c => done.contains (nameString c.name))
    unless selected.isEmpty do
      let p : System.FilePath := dest ++ "/" ++ m.replace "." "/" ++ ".olean"
      IO.FS.createDirAll p.parent.get!
      saveModuleData p m.toName { data with
        imports := #[]
        constants := selected
        constNames := selected.map (·.name)
        extraConstNames := #[]
        entries := #[] }
  pure (needed,done)
private unsafe def scan (m : String) (p : System.FilePath) (needed done : Std.HashSet String) :
    IO (Std.HashSet String × Std.HashSet String) := do
  let loaded ← parts p
  let some (data,_) := loaded.toList.getLast? | throw (IO.userError "empty")
  let result ← work m data needed done
  let regions := loaded.map (·.2)
  regions.reverse.forM CompactedRegion.free
  pure result

private unsafe def allNames (p : System.FilePath) : IO (Array String) := do
  let loaded ← parts p
  let some (data,_) := loaded.toList.getLast? | throw (IO.userError "empty factor")
  let result := data.constants.map (fun c => nameString c.name)
  let size := result.foldl (fun n s => n+s.length) (0 : Nat)
  if size > 10000000 then throw (IO.userError "unreasonable factor name bytes")
  (loaded.map (·.2)).reverse.forM CompactedRegion.free
  return result
private unsafe def mainExport : IO Unit := do
  let some inputPath ← IO.getEnv "S126_SDK_EXPORT_INPUT" | throw (IO.userError "missing input path")
  let input ← IO.FS.readFile inputPath
  let config ← IO.ofExcept (Json.parse input)
  let roots ← IO.ofExcept (config.getObjValAs? (List String) "roots")
  let modules ← IO.ofExcept (config.getObjValAs? (Array String) "modules")
  let seeds ← IO.ofExcept (config.getObjValAs? (Array String) "seeds")
  let whole ← IO.ofExcept (config.getObjValAs? (Array String) "all_declarations")
  let dest ← IO.ofExcept (config.getObjValAs? String "dest")
  let some activeDest ← IO.getEnv "S126_SDK_TRANSPORT" | throw (IO.userError "missing destination")
  unless activeDest == dest do throw (IO.userError "destination mismatch")
  let seen ← IO.mkRef ({} : Std.HashSet String)
  let order ← IO.mkRef (#[] : Array (String × System.FilePath))
  for m in modules do visit roots m seen order
  let mut needed : Std.HashSet String := {}
  for n in seeds do needed := needed.insert n
  for m in whole do
    for n in ← allNames (← findObject roots m) do needed := needed.insert n
  IO.println ("SEEDS " ++ (toJson needed.toArray).compress)
  let mut done : Std.HashSet String := {}
  for (m,p) in (← order.get).reverse do
    let (n,d) ← scan m p needed done
    needed := n
    done := d
  let unresolved := needed.toArray.filter (fun n => !done.contains n)
  IO.println ("UNRESOLVED " ++ (toJson unresolved).compress)
  IO.println ("SUMMARY " ++ (Json.mkObj [("modules",toJson (← order.get).size),
    ("constants",toJson done.size),("needed",toJson needed.size)]).compress)
  unless unresolved.isEmpty do throw (IO.userError "incomplete constant closure")
#eval mainExport

end AspisS126SdkCurrentExport
