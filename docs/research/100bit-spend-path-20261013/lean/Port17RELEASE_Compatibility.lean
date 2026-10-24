import Lean
open Lean
private def sameDeclaration (a b : ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a.toConstantVal == b.toConstantVal
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .quotInfo a, .quotInfo b => a.toConstantVal == b.toConstantVal &&
      match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | .inductInfo a, .inductInfo b =>
      a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec &&
      a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => false
private def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty module")
  pure data
#eval show IO Unit from do
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let mut replacements : Std.HashMap String System.FilePath := {}
  for line in (← IO.FS.readFile "Port17RELEASE-compare-input.tsv").splitOn "\n" do
    if line.isEmpty then continue
    let fields := line.splitOn "\t"
    replacements := replacements.insert fields[0]! fields[1]!
  let mut pending := ["Port17RELEASE_Control", "Port6AUTH_Accounting"]
  let mut visited : Std.HashSet String := {}
  while !pending.isEmpty do
    let owner := pending.head!
    pending := pending.tail!
    if visited.contains owner then continue
    visited := visited.insert owner
    let mut found : Option System.FilePath := none
    for root in roots do
      let p : System.FilePath := root ++ "/" ++ owner.replace "." "/" ++ ".olean"
      if ← p.pathExists then
        found := some p
        break
    let some before := found | throw (IO.userError s!"Missing object {owner}")
    let (header, _) ← readModuleData before
    let imports := header.imports.map (fun i => i.module.toString)
    pending := imports.toList ++ pending
    if let some after := replacements[owner]? then
      let a ← readComplete before
      let b ← readComplete after
      let mut bm : Std.HashMap Name ConstantInfo := {}
      for ci in b.constants do bm := bm.insert ci.name ci
      let mut missing : Array String := #[]
      let mut changed : Array String := #[]
      for ci in a.constants do
        match bm[ci.name]? with
        | none => missing := missing.push ci.name.toString
        | some other =>
          if !sameDeclaration ci other then changed := changed.push ci.name.toString
      IO.println ("COMPAT " ++ (Json.arr #[toJson owner, toJson before.toString,
        toJson after.toString, toJson a.constants.size, toJson b.constants.size,
        toJson missing, toJson changed]).compress)
  IO.println ("ROOT_CLOSURE_MODULES " ++ toString visited.size)
