#!/usr/bin/env python3
from pathlib import Path
import subprocess,hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';P=B/'evidence/s126-current-caller-20261021/sdk-current-export-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
path='docs/research/100bit-spend-path-20261013/lean/Port18COHERENCE_CompatibilityLoad.lean';raw=subprocess.check_output(['git','show','904745b496:'+path]).decode();helper=raw[raw.index('def sameDeclaration'):raw.index('\ndef load')]
main=r'''
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
  let some inputPath ← IO.getEnv "S126_SDK_AUDIT_INPUT" | throw (IO.userError "missing audit input")
  let input ← IO.FS.readFile inputPath
  let config ← IO.ofExcept (Json.parse input)
  let modules ← IO.ofExcept (config.getObjValAs? (Array (String × String)) "transport")
  if let .ok pair := config.getObjValAs? (String × String) "proof_refresh" then
    let old ← readComplete pair.1
    let fresh ← readComplete pair.2
    for n in ["AspisR1.S2W_EntryPrivileges.guards", "AspisR1.S2W_EntryPrivileges.readonly",
        "AspisR1.S2W_EntryPrivileges.writable", "AspisR1.S2W_EntryPrivileges.accepted_privileges"] do
      let some a := old.constants.find? (fun c => c.name == n.toName)
        | throw (IO.userError s!"missing old proof {n}")
      let some b := fresh.constants.find? (fun c => c.name == n.toName)
        | throw (IO.userError s!"missing refreshed proof {n}")
      let sameType := a.type == b.type
      IO.println ("PROOF_REFRESH " ++ (Json.mkObj [("name",toJson n),
        ("same_type",toJson sameType),("old_theorem",toJson a.isTheorem),
        ("new_theorem",toJson b.isTheorem)]).compress)
      unless sameType && a.isTheorem && b.isTheorem do
        throw (IO.userError s!"proof refresh changed the complete statement: {n}")
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
      IO.println ("UNSAFE_OR_PARTIAL " ++ (toJson n.toString).compress)
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
'''
s='import Lean\nopen Lean\nnamespace AspisS126SdkTransportAudit\n'+helper+'\n'+main+'\nend AspisS126SdkTransportAudit\n';(S/'S126SdkTransportAuditV1.lean').write_text(s)
(P/'audit-source.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_path=path,source_revision='904745b496',source_sha256=hashlib.sha256(raw.encode()).hexdigest(),copied_helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),scope='Untrusted transport structure/dependency/strict duplicate audit only; no environment insertion or kernel checking.'),indent=2)+'\n')
print(json.dumps(dict(bytes=len(s.encode()))))
