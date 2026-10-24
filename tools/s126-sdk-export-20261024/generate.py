#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';P=B/'evidence/s126-current-caller-20261021/sdk-current-export-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
path='docs/research/100bit-spend-path-20261013/lean/Port18COHERENCE_RootSnapshot.lean';raw=subprocess.check_output(['git','show','904745b496:'+path]).decode();body=raw[raw.index('private def clone'):raw.index('private unsafe def mainDiagnostic')]
# Preserve exact old reader/region lifetime/saveModuleData machinery. Extend
# group dependencies to every mutual inductive recursor, not merely used recursors.
body=body.replace('if let .inductInfo v := c then ds := ds ++ v.ctors.toArray ++ v.all.toArray','if let .inductInfo v := c then\n      ds := ds ++ v.ctors.toArray ++ v.all.toArray ++ (v.all.toArray.map (· ++ `rec))')
body=body.replace('if let some dest ← IO.getEnv "PORT18_SNAPSHOT" then','if let some dest ← IO.getEnv "S126_SDK_TRANSPORT" then')
main=r'''
private unsafe def allNames (p : System.FilePath) : IO (Array String) := do
  let loaded ← parts p
  let some (data,_) := loaded.toList.getLast? | throw (IO.userError "empty factor")
  let result := data.constants.map (fun c => nameString c.name)
  let size := result.foldl (fun n s => n+s.length) (0 : Nat)
  if size > 10000000 then throw (IO.userError "unreasonable factor name bytes")
  (loaded.map (·.2)).reverse.forM CompactedRegion.free
  return result
private unsafe def mainExport : IO Unit := do
  let some inputPath ← IO.getEnv "S126_SDK_EXPORT_INPUT" | throw (IO.userError "missing input path")
  let input ← IO.FS.readFile inputPath
  let config ← IO.ofExcept (Json.parse input)
  let roots ← IO.ofExcept (config.getObjValAs? (List String) "roots")
  let modules ← IO.ofExcept (config.getObjValAs? (Array String) "modules")
  let seeds ← IO.ofExcept (config.getObjValAs? (Array String) "seeds")
  let whole ← IO.ofExcept (config.getObjValAs? (Array String) "all_declarations")
  let dest ← IO.ofExcept (config.getObjValAs? String "dest")
  let some activeDest ← IO.getEnv "S126_SDK_TRANSPORT" | throw (IO.userError "missing destination")
  unless activeDest == dest do throw (IO.userError "destination mismatch")
  let seen ← IO.mkRef ({} : Std.HashSet String)
  let order ← IO.mkRef (#[] : Array (String × System.FilePath))
  for m in modules do visit roots m seen order
  let mut needed : Std.HashSet String := {}
  for n in seeds do needed := needed.insert n
  for m in whole do
    for n in ← allNames (← findObject roots m) do needed := needed.insert n
  IO.println ("SEEDS " ++ (toJson needed.toArray).compress)
  let mut done : Std.HashSet String := {}
  for (m,p) in (← order.get).reverse do
    let (n,d) ← scan m p needed done
    needed := n
    done := d
  let unresolved := needed.toArray.filter (fun n => !done.contains n)
  IO.println ("UNRESOLVED " ++ (toJson unresolved).compress)
  IO.println ("SUMMARY " ++ (Json.mkObj [("modules",toJson (← order.get).size),
    ("constants",toJson done.size),("needed",toJson needed.size)]).compress)
  unless unresolved.isEmpty do throw (IO.userError "incomplete constant closure")
#eval mainExport
'''
out='import Lean\nopen Lean\nnamespace AspisS126SdkCurrentExport\n'+body+main+'\nend AspisS126SdkCurrentExport\n';(S/'S126SdkCurrentExportV1.lean').write_text(out)
(P/'exporter-source.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_path=path,source_revision='904745b496',source_sha256=hashlib.sha256(raw.encode()).hexdigest(),original_helper_span_sha256=hashlib.sha256(raw[raw.index('private def clone'):raw.index('private unsafe def mainDiagnostic')].encode()).hexdigest(),changes=['New owning-session namespace/config/seeds/destination','Retain every factor declaration as seed','Add each mutually grouped inductive recursor as dependency','No change to raw module serialization, complete value discovery or region lifetime handling'],assessment='Untrusted declaration transport only; no theorem import, environment insertion or kernel validation occurs here.'),indent=2)+'\n')
print(json.dumps(dict(bytes=len(out.encode()))))
