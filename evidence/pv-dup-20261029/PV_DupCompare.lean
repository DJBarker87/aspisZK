import Lean
open Lean
unsafe def loadParts (path : String) : IO (Array (ModuleData × CompactedRegion)) := do
  let base ← readModuleData path
  if base.1.isModule then
    let server ← CompactedRegion.read (α := ModuleData) (path ++ ".server") #[base.2]
    let priv ← CompactedRegion.read (α := ModuleData) (path ++ ".private") #[base.2, server.2]
    return #[base, server, priv]
  return #[base]

def getConstant (parts : Array (ModuleData × CompactedRegion)) (name : String) : Option ConstantInfo := Id.run do
  let mut result := none
  for p in parts do
    for c in p.1.constants do
      if c.name.toString == name then result := some c
  return result

@[noinline] unsafe def comparePair (line : String) : IO (Array CompactedRegion) := do
  let f := line.splitOn "\t"
  let a ← loadParts f[2]!
  let b ← loadParts f[4]!
  let ca := (getConstant a f[0]!).get!
  let cb := (getConstant b f[0]!).get!
  let ta := reprStr ca.type
  let tb := reprStr cb.type
  let va := (ca.value? true).map reprStr
  let vb := (cb.value? true).map reprStr
  let j := Json.mkObj [("name",toJson f[0]!), ("left_module",toJson f[1]!), ("right_module",toJson f[3]!),
    ("type_equal",toJson (ta == tb)), ("value_equal",toJson (va == vb)),
    ("level_params_equal",toJson (ca.levelParams == cb.levelParams)),
    ("constant_info_equal",toJson (reprStr ca == reprStr cb)),
    ("left_type",toJson ta), ("right_type",toJson tb), ("left_value",toJson va), ("right_value",toJson vb)]
  (← IO.getStdout).putStrLn j.compress
  (← IO.getStdout).flush
  return (a ++ b).map (·.2)

unsafe def main (args : List String) : IO Unit := do
  for line in (← IO.FS.lines args[0]!) do
    let regions ← comparePair line
    for r in regions.reverse do CompactedRegion.free r
