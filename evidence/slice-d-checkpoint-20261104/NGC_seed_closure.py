"""Copy only the once-selected coherent object closure, retaining ordered resolution."""
from pathlib import Path
import json,subprocess,lzma,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
rows=[]
for path in [E.parent/'slice-q-accum-20261104/NFS_EXPECTED_IMPORTS.jsonl',E.parent/'slice-d-check-20261104/NFU_EXPECTED_IMPORTS.jsonl',E.parent/'slice-d-check-20261104/NFU_QUERY_EXPECTED_IMPORTS.jsonl']:
 if path.exists():rows += [json.loads(l) for l in path.read_text().splitlines()]
modules=sorted({r['module'] for r in rows})
prior=json.loads((E.parent/'slice-d-check-20261104/NFU_L057/receipt.json').read_text())['env']['LEAN_PATH'].split(':')
code=f'''from pathlib import Path
import json,hashlib,subprocess,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-20261104');c=Path('/home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-cache-20261104')
p=b/'NGC_CLOSURE-admission.json'
with (b/'NGC_CLOSURE-barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(p.read_text());print(json.dumps(dict(exit=r.returncode,allowed=a['allowed'])),flush=True)
if r.returncode!=0 or a['allowed']is not True:sys.exit(78)
roots=[c/'NFU_exports_20261104',c/'NFT_exports_20261104',c/'NFS_exports_20261104',c/'NFP_exports_20261104']+[Path(s)for s in {prior!r}]
# Output is a private flattened fallback; earlier explicit exports still take precedence.
out=c/'NGC_selected_closure';out.mkdir(exist_ok=True);pins=[];missing=[]
for m in {modules!r}:
 rel=m.replace('.','/')
 src=next((r/(rel+'.olean') for r in roots if (r/(rel+'.olean')).is_file()),None)
 if src is None:missing.append(m);continue
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=src.with_name(src.name[:-6]+suffix)
  if not p.is_file():continue
  q=out/(rel+suffix);q.parent.mkdir(parents=True,exist_ok=True)
  data=p.read_bytes();q.write_bytes(data);pins.append(dict(source=str(p),target=str(q),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
x=dict(modules=len({modules!r}),selected_files=len(pins),selected_bytes=sum(p['bytes']for p in pins),missing=missing,pins=pins)
(b/'NGC_CLOSURE.json').write_text(json.dumps(x));print(json.dumps({{k:v for k,v in x.items()if k!='pins'}}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input=code,text=True,capture_output=True)
(E/'NGC_CLOSURE-local.log').write_text(r.stdout+r.stderr);print(r.stdout[-1800:]);assert r.returncode==0,r.stderr
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat /home/dombarker/project-offloads/codex-cx-slice-d-checkpoint-20261104/NGC_CLOSURE.json'],capture_output=True);assert r.returncode==0
(E/'NGC_CLOSURE.json.xz').write_bytes(lzma.compress(r.stdout));(E/'NGC_CLOSURE.json.sha256').write_text(hashlib.sha256(r.stdout).hexdigest()+'\n')
