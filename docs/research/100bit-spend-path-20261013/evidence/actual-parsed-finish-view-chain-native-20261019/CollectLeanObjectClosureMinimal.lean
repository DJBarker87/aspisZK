import Lean.Environment
open Lean
set_option autoImplicit false
partial def collect (roots : Array System.FilePath) (todo : List String)
    (seen : Std.HashSet String) (out : Array Json) : IO (Array Json) := do
  match todo with
  | [] => pure out
  | m :: rest =>
    if seen.contains m then return ← collect roots rest seen out
    let rel := (m.replace "." "/") ++ ".olean"
    let mut found : Option System.FilePath := none
    for root in roots do
      let path := root / rel
      if ← path.pathExists then
        found := some path
        break
    let some path := found | throw (IO.userError s!"Missing object {m}")
    let (data, _) ← readModuleData path
    let deps := data.imports.toList.map (fun i => i.module.toString)
    let row := Json.mkObj [("module", toJson m), ("path", toJson path.toString),
      ("imports", toJson deps)]
    collect roots (deps ++ rest) (seen.insert m) (out.push row)
def main (args : List String) : IO Unit := do
  let rootFile :: mods := args | throw (IO.userError "roots file then modules required")
  let roots := (← IO.FS.lines rootFile).map System.FilePath.mk
  let rows ← collect roots mods {} #[]
  IO.println (Json.arr rows).compress
