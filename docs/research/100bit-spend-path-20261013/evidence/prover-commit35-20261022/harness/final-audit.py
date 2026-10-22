#!/usr/bin/env python3
"""Audit text receipts and exact final source/object dependency pins."""
import hashlib,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
rows=json.loads((E/'lean/attempts.json').read_text())
latest={}
for r in rows:
 if r['exit_status']==['0']:latest[r['module']]=r
mods=[]
for m,r in latest.items():
 p=L/m
 assert p.exists(),m
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if sha!=r['source_sha256']:
  raise AssertionError((m,'final source differs from latest accepted receipt'))
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   ax=set(re.search(r'\[(.*?)\]',line,re.S)[1].replace('\n','').split(','))
   assert {a.strip() for a in ax} <= {'propext','Classical.choice','Quot.sound'},line
 assert r['swaps']=='0',(m,r['swaps'])
 mods.append(dict(module=m,source_sha256=sha,attempt=r['attempt'],deps=r['deps'],exit_status=r['exit_status'],wall=r['wall'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],print_axioms=r['print_axioms']))
remote='''import hashlib,json
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
mods=json.loads(%r)
out=[]
for m in mods:
 p=J/'sources'/m['module'];o=J/'objects'/Path(m['module']).with_suffix('.olean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==m['source_sha256'],m['module']
 assert o.exists(),m['module']
 deps=[]
 for name,sha in m.pop('deps'):
  # Search the same Env J path order as the launcher.
  env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
  paths=[J/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
  rel=Path(name.replace('.','/')+'.olean')
  d=next((q/rel for q in paths if (q/rel).exists()),None)
  assert d and hashlib.sha256(d.read_bytes()).hexdigest()==sha,(m['module'],name,'changed dependency')
  deps.append(dict(module=name,sha256=sha))
 m['object_sha256']=hashlib.sha256(o.read_bytes()).hexdigest();m['dependencies_verified']=deps
 out.append(m)
print(json.dumps(out))
'''%json.dumps(mods)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=remote,text=True,capture_output=True,check=True)
checked=json.loads(r.stdout)
changed=subprocess.check_output(['git','diff','--name-only','6b5544772','--','crates','programs'],text=True).splitlines()
assert not changed,changed
record=dict(source_base_revision='6b5544772',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),audit_checkout_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_identity='base plus exact source overlay SHA256 and dependency-object pins',modules=checked,shipped_files_changed=changed,elf_rebuild_required=False,full_manifest_replayed=False,target_established=False,stop_interface='Faithful create_new private-ledger transition/exposure law; status-only schedule cannot implement path-sensitive duplicates. Native publication and source-to-FS conversion remain open')
(E/'final-proof-audit.json').write_text(json.dumps(record,indent=2)+'\n')
(E/'shipped-sources-unchanged.json').write_text(json.dumps({k:record[k] for k in ['source_base_revision','audit_checkout_revision','shipped_files_changed','elf_rebuild_required']},indent=2)+'\n')
print(json.dumps(dict(accepted_final_modules=len(checked),shipped_files_changed=changed,target_established=False)))
