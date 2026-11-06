"""Read-only closure hashing plus copying owned export, after all scopes end."""
from pathlib import Path
import json,subprocess,lzma,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-batch-merkle3-20261108'
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(B);env=json.loads((b/'NKL_ENV.json').read_text());roots=env['LEAN_PATH'].split(':')+[env['LEAN_SYSROOT']+'/lib/lean']
rows=[json.loads(s) for s in (b/'NKL_LOADED_scan.jsonl').read_text().splitlines()]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
selected=[]
for row in rows:
 m=row['module'];rel=m.replace('.','/')+'.olean';p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None)
 assert p is not None,m
 selected.append(dict(module=m,path=str(p),sha256=sha(p),bytes=p.stat().st_size))
inv=json.loads((b/'NKL_PROOF_INVENTORY.json').read_text());export=b/'NKL_exports_final_20261108';export.mkdir(exist_ok=True);files=[]
for m in list(inv['modules'])+['NKL_COMBINED_IMPORT']:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=b/'NKL_objects'/(m+suffix)
  if p.is_file():
   q=export/p.name
   if q.exists():assert sha(q)==sha(p)
   else:shutil.copy2(p,q)
   files.append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size))
print(json.dumps(dict(LEAN_PATH=env['LEAN_PATH'],modules=len(rows),selected_objects=selected,scan_pass=True,export=dict(path=str(export),files=files,total_bytes=sum(f['bytes'] for f in files)),host_disk_free=shutil.disk_usage(b).free,own_bytes=int(__import__('subprocess').check_output(['du','-sb',str(b)],text=True).split()[0]))))
'''.replace('B)',repr(B)+')')
code=code.replace("inv=json.loads((b/'NKL_PROOF_INVENTORY.json').read_text())","inv="+repr(json.loads((E/'NKL_PROOF_INVENTORY.json').read_text())))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NKL_CLOSURE_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr))+'\n');assert r.returncode==0,r.stderr
raw=r.stdout.encode();x=json.loads(raw);p=E/'NKL_CLOSURE_PINS.json';p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NKL_EXPORT.json').write_text(json.dumps(x['export'],indent=2)+'\n');print('NKL closure pinned: '+str(x['modules'])+' modules; export '+str(x['export']['total_bytes'])+' bytes')
