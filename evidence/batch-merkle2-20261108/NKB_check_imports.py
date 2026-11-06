"""Read-only complete import-closure availability and selected-object pins."""
from pathlib import Path
import os,json,hashlib
E=Path.cwd();expected={}
for line in (E/'NKB_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
 x=json.loads(line);expected[x['module']]=x['imports']
wanted=set();todo=['NKB_COMBINED_IMPORT'];unknown=[]
while todo:
 name=todo.pop()
 if name in wanted:continue
 wanted.add(name)
 if name not in expected:unknown.append(name)
 else:todo.extend(expected[name])
T=Path(os.environ['LEAN_SYSROOT']);roots=[E/'.lake/build/lib/lean',T/'lib/lean']+[Path(p) for p in os.environ['LEAN_PATH'].split(':')]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
missing=[];objects={}
for name in sorted(wanted-{'NKB_COMBINED_IMPORT'}):
 rel=name.replace('.','/')+'.olean';p=next((root/rel for root in roots if (root/rel).is_file()),None)
 if p is None:missing.append(name);continue
 objects[name]=[dict(path=str(q),bytes=q.stat().st_size,sha256=sha(q)) for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')] if q.is_file()]
result=dict(root='NKB_COMBINED_IMPORT',module_count=len(wanted),missing=missing,unknown_expected_imports=unknown,selected_objects=objects,search_path=[str(p) for p in roots],cargo_target=os.environ['CARGO_TARGET_DIR'])
(E/'NKB_IMPORT_PREFLIGHT.json').write_text(json.dumps(result,indent=2)+'\n');print('NKB import preflight: '+str(len(wanted))+' modules, missing='+str(len(missing))+', unknown='+str(len(unknown)))
assert not missing and not unknown,(missing,unknown)
