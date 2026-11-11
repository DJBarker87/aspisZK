import Lean
open Lean
unsafe def main (args : List String) : IO Unit := do
  let root := args[0]!
  let lst ← IO.FS.lines args[1]!
  let out ← IO.FS.Handle.mk args[2]! .write
  for rel in lst do
    let (md, reg) ← readModuleData (root ++ "/" ++ rel)
    let mods := md.imports.map (fun i => toString i.module)
    out.putStrLn (rel ++ "\t" ++ String.intercalate "," mods.toList)
    reg.free
