import Lean
open Lean
#eval show IO Unit from do
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let known := (← IO.FS.readFile "Port17RELEASE-known-A.txt").splitOn "\n"
  let mut pending := ["Port17RELEASE_Control", "Port17RELEASE_Invariant", "Port6AUTH_Accounting"]
  let mut visited : Std.HashSet String := {}
  while !pending.isEmpty do
    let owner := pending.head!
    pending := pending.tail!
    if visited.contains owner then continue
    visited := visited.insert owner
    if known.contains owner then continue
    let mut found : Option System.FilePath := none
    for root in roots do
      let p : System.FilePath := root ++ "/" ++ owner.replace "." "/" ++ ".olean"
      if ← p.pathExists then
        found := some p
        break
    let some p := found | throw (IO.userError s!"Missing root object {owner}")
    let (data, _region) ← readModuleData p
    let imports := data.imports.map (fun i => i.module.toString)
    IO.println ("ROOT_MODULE " ++ (Json.arr #[toJson owner, toJson p.toString, toJson imports]).compress)
    pending := imports.toList ++ pending
