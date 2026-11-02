"""Proof-only literal-bound elaboration; all computational source is preserved."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-uc-20261029';L=R/'tools/pv-uc-20261029/lean'
source=(L/'PVUCReadyEntry/Funs.lean').read_text()
pattern=r'\btoStr ("(?:[^"\\]|\\.)*")'
strings=[json.loads(m[1]) for m in re.finditer(pattern,source)]
assert strings and all(s.isascii() and len(s.encode())<64 for s in strings)
proof=' (by rw [_root_.String.size_toByteArray]; decide)'
s=re.sub(pattern,lambda m:m[0]+proof,source)
s=s.replace('namespace PV_UC_ReadyEntry\n','namespace PV_UC_StandardEntry\nopen PV_UC_ReadyEntry\n').replace('end PV_UC_ReadyEntry\n','end PV_UC_StandardEntry\n')
inverse=s.replace(proof,'').replace('namespace PV_UC_StandardEntry\nopen PV_UC_ReadyEntry\n','namespace PV_UC_ReadyEntry\n').replace('end PV_UC_StandardEntry\n','end PV_UC_ReadyEntry\n')
assert inverse==source
# Existing cached types/external bindings are reused. Importing the original
# Funs is deliberately avoided by the emitted imports; the audit may still
# inventory it through imported formatter proofs, and must mark it unreachable.
s=s.replace('import PVUCReadyEntry.FunsExternal','import PVUCReadyEntry.FunsExternal\nimport PV_UC_RawAudit\nimport PV_UC_FinalPublicFormatting')
s+='\nend\n\n' # close emitted noncomputable section before executable audit helper
raw=(L/'PV_UC_RawAudit.lean').read_text();body=raw.split('namespace PV_UC_RawAudit\n',1)[1].rsplit('end PV_UC_RawAudit',1)[0]
body=body.replace('  let some rootIdx := env.getModuleIdxFor? root | throwError "root module missing"\n  let rootModule := env.header.modules[rootIdx]!.module', '''  let rootModule := match env.getModuleIdxFor? root with
    | some i => env.header.modules[i]!.module
    | none => env.header.mainModule''')
body=body.replace('  let mut todo := #[rootModule]', '''  modules := modules.insert env.header.mainModule (env.header.imports.map (·.module))
  let mut todo := #[rootModule]''')
body=body.replace('  for n in allAxioms.toArray do', '''  logInfo m!"NDP_MODULE {(Json.mkObj [("module", toJson env.header.mainModule.toString),
    ("imports", toJson (env.header.imports.map (·.module.toString))),
    ("in_root_import_closure", toJson (closure.contains env.header.mainModule))]).compress}"
  for n in allAxioms.toArray do''')
body=body.replace('("loaded_modules", toJson env.header.modules.size)', '("loaded_modules", toJson (env.header.modules.size + 1))')
body=body.replace('  logInfo "NDP_AUDIT_COMPLETE"', '''  unless walked.all (fun n => n == "propext" || n == "Classical.choice" || n == "Quot.sound") do
    throwError "nonstandard reachable axiom in standard entry: {walked}"
  logInfo "NDP_AUDIT_COMPLETE"''')
s+='open Lean Elab Command\nnamespace PV_UC_LocalRawAudit\n'+body+'\nend PV_UC_LocalRawAudit\n'
s+='''
#print axioms PV_UC_StandardEntry.main
run_cmd do
  let dir := "/home/dombarker/project-offloads/codex-pv-uc-20261029/final-gates/d561/standard-axioms"
  liftIO <| IO.FS.createDirAll dir
  PV_UC_LocalRawAudit.audit ``PV_UC_StandardEntry.main (dir ++ "/main")
'''
p=L/'PV_UC_StandardEntry.lean';p.write_text(s)
sha=lambda b:hashlib.sha256(b).hexdigest()
(E/'standard-entry-provenance.json').write_text(json.dumps(dict(status='PREPARED proof-only replacement of implicit native string-bound certificates',input_source='tools/pv-uc-20261029/lean/PVUCReadyEntry/Funs.lean',input_sha256=sha(source.encode()),output_source=str(p.relative_to(R)),output_sha256=sha(s.encode()),inverse_source_check=True,computational_edits=False,namespace_change='PV_UC_ReadyEntry to PV_UC_StandardEntry; original carrier/operation parameters imported and unchanged',literal_calls=len(strings),maximum_literal_bytes=max(len(s.encode()) for s in strings),literal_strings=strings,replacement='toStr literal h with explicit h proved by String.size_toByteArray then kernel decide; no new native decision, axiom, library edit or Rust change',audit_helper='Own raw-audit helper extended only for current module imports; current kernel declarations audited before serialization; imported serialized/kernel axiom inventories still compared',rejected_original_audit='lean75039: original main reaches 42 compiler-created native string-bound axioms; other seven roots standard-only'),indent=2)+'\n')
print(json.dumps(dict(literal_calls=len(strings),max_bytes=max(map(len,strings)),bytes=p.stat().st_size)))
