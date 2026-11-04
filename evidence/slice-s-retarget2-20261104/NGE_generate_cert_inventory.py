"""Kernel-loaded declaration/owner/type inventory for every selected name."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent;x=json.loads((E/'NGE_CERTIFICATES.json').read_text());by={}
for row in x['rows']:
 for t in row['theorems']:
  n=t['canonical_name'];m=t['canonical_module']
  assert n not in by or by[n]==m,(n,by.get(n),m)
  by[n]=m
names=sorted(by);groups=[names[i::13] for i in range(13)]
for i,ns in enumerate(groups):
 code='''import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
'''
 if i==0:code+=' logInfo m!"NGE_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"\n'
 code+=' for n in (#['+','.join('`'+n for n in ns)+'''] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
'''
 (E/f'NGE_CertificatePart{i:02}.lean').write_text(code)
(E/'NGE_CERT_INVENTORY_INPUT.json').write_text(json.dumps(dict(expected_owners=by,groups=groups,method='All 257 selected names, including absent chain B; actual checked environment ConstantInfo type and owning module index'),indent=1)+'\n')
print(json.dumps(dict(names=len(names),parts=len(groups))))
