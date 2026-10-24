import Lean
open Lean
private def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty")
  pure data
private def findObject (roots : List String) (n : String) : IO System.FilePath := do
  for root in roots do
    let p : System.FilePath := root ++ "/" ++ n.replace "." "/" ++ ".olean"
    if ← p.pathExists then return p
  throw (IO.userError s!"Missing object {n}")
private partial def visit (roots : List String) (n : String)
    (seen : IO.Ref (Std.HashSet String)) (order : IO.Ref (Array (String × System.FilePath))) : IO Unit := do
  if (← seen.get).contains n then return
  seen.modify (·.insert n)
  let p ← findObject roots n
  let (data, _) ← readModuleData p
  for i in data.imports do visit roots i.module.toString seen order
  order.modify (·.push (n,p))
#eval show IO Unit from do
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "missing path")
  let roots := path.splitOn ":"
  let seen ← IO.mkRef ({} : Std.HashSet String)
  let order ← IO.mkRef (#[] : Array (String × System.FilePath))
  for m in ["Port17RELEASE_Control", "Port17RELEASE_Invariant", "Port6AUTH_Accounting"] do
    visit roots m seen order
  let seeds := #[`AspisR1.Port17RELEASE_Control.rust, `AspisR1.Port17RELEASE_Invariant.tx1,
    `AspisR1.Port17RELEASE_Invariant.tx2, `AspisR1.Port6AUTH_Accounting.first_reads,
    `AspisR1.Port1_Driver.rust, `AspisR1.Port1_Driver.stages,
    `AspisR1.VTop_Flow.tx1, `AspisR1.VTop_Flow.tx2_authenticated,
    `AspisR1.Port1_StoredCarrier.source]
  let mut needed : Std.HashSet Name := {}
  for n in seeds do needed := needed.insert n
  let mut done : Std.HashSet Name := {}
  for (m,p) in (← order.get).reverse do
    let data ← readComplete p
    let mut cs : Std.HashMap Name ConstantInfo := {}
    for c in data.constants do cs := cs.insert c.name c
    let mut pending := data.constNames.toList.filter needed.contains
    while !pending.isEmpty do
      let n := pending.head!
      pending := pending.tail!
      if done.contains n then continue
      done := done.insert n
      let some c := cs[n]? | throw (IO.userError s!"missing local {n}")
      let mut ds := c.type.getUsedConstants
      if let some v := c.value? then ds := ds ++ v.getUsedConstants
      if let .inductInfo v := c then ds := ds ++ v.ctors.toArray
      IO.println ("EDGE " ++ (Json.arr #[toJson m,toJson n.toString,toJson (ds.map Name.toString)]).compress)
      for d in ds do
        needed := needed.insert d
        if cs.contains d && !done.contains d then pending := d :: pending
  let unresolved := needed.toArray.filter (fun n => !done.contains n)
  IO.println ("UNRESOLVED " ++ (toJson (unresolved.map Name.toString)).compress)
  IO.println s!"SUMMARY modules={(← order.get).size} constants={done.size}"
