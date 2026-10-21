#!/usr/bin/env python3
"""Check inherited caller-translation failures against unchanged source bodies."""
import hashlib,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
old=E.parent/'prover-commit2-20261020'
base='f2a598c6a'
def sha(b):return hashlib.sha256(b).hexdigest()
def body(s,name):
 m=re.search(r'^( *)[^\n]*\bfn '+re.escape(name)+r'\s*[(<]',s,re.M)
 assert m,name
 end=s.index('\n'+m[1]+'}',m.end())+len(m[1])+2
 return s[m.start():end].encode()
rows=[]
for rel,names in {
 'crates/aspis-prover/src/state_only_hiding.rs':['build_mask_material_for_layout','balance_m31_copy_inactive','balance_qm31_copy_inactive'],
 'crates/aspis-prover/src/state_only_entropy.rs':['derive_pool_v1_zero_factor_d']}.items():
 now=Path(rel).read_text()
 before=subprocess.check_output(['git','show',base+':'+rel],text=True)
 for name in names:
  a,b=body(now,name),body(before,name)
  rows.append(dict(path=rel,function=name,sha256=sha(a),bytes=len(a),old_revision=base,
   old_sha256=sha(b),unchanged=a==b))
assert all(x['unchanged'] for x in rows)
receipts=[]
for label in ['builder-charon','builder-aeneas','builder-d-carried-aeneas','builder-all-carried-aeneas']:
 p=old/label/'receipt.json';r=json.loads(p.read_text())
 receipts.append(dict(path=str(p),sha256=sha(p.read_bytes()),exit=r['exit_status'],wall=r['wall_seconds'],
  peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],command=r['command'],print_axioms=r['print_axioms']))
tools=json.loads((old/'builder-aeneas-source-pins.json').read_text())['tools']
for tool in tools:
 actual=subprocess.check_output(['ssh','dombarker@100.108.41.90','sha256sum '+tool['path']],text=True).split()[0]
 assert actual==tool['sha256']
 tool['current_sha256']=actual
 tool['unchanged']=True
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 current_functions=rows,inherited_translation_receipts=receipts,tool_identity=tools,
 production_elf_check="frozen-elf-final-check.json",
 interpretation='Inherited failed aggregate source translations remain failed evidence; no unchanged aggregate translation rerun; new proof configuration changes trigger one final ELF comparison. Component and new mathematical decoder laws do not install an aggregate Rust caller identity.')
(E/'source-frontier.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(unchanged_functions=len(rows),production_changes=False)))
