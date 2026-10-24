import Lean
open Lean
namespace AspisS126SdkTransportAudit
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


def dependencies (c : ConstantInfo) : Array Name := Id.run do
  let mut ds := c.type.getUsedConstants
  if let some value := c.value? (allowOpaque := true) then ds := ds ++ value.getUsedConstants
  if let .inductInfo v := c then
    ds := ds ++ v.all.toArray ++ v.ctors.toArray ++ (v.all.toArray.map (· ++ `rec))
  if let .recInfo v := c then
    ds := ds ++ v.all.toArray
    for rule in v.rules do ds := ds ++ rule.rhs.getUsedConstants
  return ds

def audit : IO Unit := do
  let input ← IO.FS.readFile "/private/tmp/s126-sdk-current-export-20261024-v1/audit-input.json"
  let config ← IO.ofExcept (Json.parse input)
  let modules ← IO.ofExcept (config.getObjValAs? (Array (String × String)) "transport")
  let seeds ← IO.ofExcept (config.getObjValAs? (Array String) "seeds")
  let mut cs : Std.HashMap Name ConstantInfo := {}
  let mut owners : Std.HashMap Name String := {}
  let mut duplicateCount := 0
  let mut conflicts := 0
  for (module,path) in modules do
    let data ← readComplete path
    unless data.imports.isEmpty && data.extraConstNames.isEmpty && data.entries.isEmpty do
      throw (IO.userError s!"nonempty transport import/extension fields: {module}")
    unless data.constNames == data.constants.map (·.name) do
      throw (IO.userError s!"constant name table mismatch: {module}")
    for c in data.constants do
      if let some old := cs[c.name]? then
        duplicateCount := duplicateCount+1
        let same := sameDeclaration old c
        IO.println ("DUPLICATE " ++ (Json.mkObj [("name",toJson c.name.toString),
          ("first",toJson owners[c.name]!), ("second",toJson module),
          ("identical",toJson same)]).compress)
        unless same do
          conflicts := conflicts+1
          IO.println ("CONFLICT_FULL " ++ (Json.mkObj [("name",toJson c.name.toString),
            ("first_type",toJson (reprStr old.type)), ("first_value",toJson (reprStr (old.value? (allowOpaque := true)))),
            ("second_type",toJson (reprStr c.type)), ("second_value",toJson (reprStr (c.value? (allowOpaque := true))))]).compress)
      else
        cs := cs.insert c.name c
        owners := owners.insert c.name module
  let mut unresolved : Std.HashSet String := {}
  for (n,c) in cs.toArray do
    if c.isUnsafe || c.isPartial then
      IO.println ("UNSAFE_OR_PARTIAL " ++ toJson n.toString |>.compress)
    for dep in dependencies c do
      unless cs.contains dep do unresolved := unresolved.insert dep.toString
    IO.println ("CONSTANT " ++ (Json.mkObj [("name",toJson n.toString),
      ("module",toJson owners[n]!), ("dependencies",toJson ((dependencies c).map Name.toString))]).compress)
  let missingSeeds := seeds.filter (fun n => !cs.contains n.toName)
  IO.println ("AUDIT_SUMMARY " ++ (Json.mkObj [("modules",toJson modules.size),
    ("constants",toJson cs.size),("duplicates",toJson duplicateCount),
    ("conflicts",toJson conflicts),("unresolved",toJson unresolved.toArray),
    ("missing_seeds",toJson missingSeeds)]).compress)
  unless conflicts == 0 && unresolved.isEmpty && missingSeeds.isEmpty do
    throw (IO.userError "transport conflicts or incomplete closure; not accepted")
#eval audit

end AspisS126SdkTransportAudit
