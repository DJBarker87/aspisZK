import Lean
open Lean
@[noinline] unsafe def inspect (line : String) : IO (Array CompactedRegion) := do
  let f := line.splitOn "\t"
  let (d,r) ← readModuleData f[1]!
  let stdout ← IO.getStdout
  for c in d.constants do
    if f[2]! == c.name.toString then
      if let .inductInfo v := c then
        stdout.putStrLn <| (Json.mkObj [("module",toJson f[0]!), ("type",toJson c.name.toString),
          ("constructors",toJson (v.ctors.map Name.toString)),("constructor_count",toJson v.ctors.length)]).compress
  stdout.flush
  return #[r]
unsafe def main (args : List String) : IO Unit := do
  for line in (← IO.FS.lines args[0]!) do
    let rs ← inspect line
    for r in rs do CompactedRegion.free r
