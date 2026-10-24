import Lean
open Lean
namespace AspisS6SdkDeclarationAudit
def sameDeclaration (a b : ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
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
def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty module")
  pure data


def run : IO Unit := do
  let input ← IO.FS.readFile "/tmp/s126-sdk-declaration-audit-20261024.json"
  let j ← IO.ofExcept (Json.parse input)
  let rows ← IO.ofExcept j.getArr?
  let mut originals : Std.HashMap Name ConstantInfo := {}
  let mut factors : Array ConstantInfo := #[]
  for row in rows do
    let path ← IO.ofExcept (row.getObjValAs? String "path")
    let factored ← IO.ofExcept (row.getObjValAs? Bool "factored")
    let data ← readComplete path
    for c in data.constants do
      if factored then factors := factors.push c
      else originals := originals.insert c.name c
  let mut missing := 0
  let mut identical := 0
  let mut proofOnly := 0
  let mut different := 0
  for c in factors do
    if let some old := originals[c.name]? then
      if c.name == `AspisR1.S2W_D189Wrappers.first then
        IO.println ("FIRST_TERMS " ++ (Json.mkObj [("original",toJson (reprStr old.value?)),
          ("factored",toJson (reprStr c.value?))]).compress)
      let same := sameDeclaration old c
      let sameType := old.type == c.type
      let sameValue := old.value? (allowOpaque := true) == c.value? (allowOpaque := true)
      let proof := old.isTheorem && c.isTheorem && sameType
      IO.println ("DECL " ++ (Json.mkObj [("name",toJson c.name.toString),
        ("identical",toJson same),("same_type",toJson sameType),
        ("same_value",toJson sameValue),("proof_only",toJson proof)]).compress)
      if same then identical := identical+1
      else if proof then proofOnly := proofOnly+1
      else different := different+1
    else
      missing := missing+1
      IO.println ("MISSING " ++ c.name.toString)
  IO.println ("SUMMARY " ++ (Json.mkObj [("identical",toJson identical),
    ("proof_only",toJson proofOnly),("different",toJson different),("missing",toJson missing)]).compress)
#eval run
end AspisS6SdkDeclarationAudit
