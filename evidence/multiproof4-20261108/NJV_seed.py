from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-multiproof4-20261108'
C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJV_20261108'
script=f'''from pathlib import Path
import json,subprocess,hashlib,shutil,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/'NJV_seed_admission.json'
with (b/'NJV_seed_barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(p.read_text()) if p.exists() else {{}}
if r.returncode!=0 or a.get('allowed') is not True:
 print(json.dumps(dict(admission=a,exit=r.returncode)));sys.exit(78)
imports=[]
for src,name in [('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJP_20261108/NJP_exports_20261108','NJV_NJP_seed'),('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NJO_20261108/NJO_exports_20261108','NJV_NJO_seed')]:
 dst=Path({C!r})/name;dst.mkdir(parents=True,exist_ok=True)
 for z in sorted(Path(src).rglob('*')):
  if not z.is_file():continue
  target=dst/z.relative_to(src);target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists():assert target.read_bytes()==z.read_bytes()
  else:shutil.copy2(z,target)
  imports.append(dict(source=str(z),path=str(target),size=z.stat().st_size,sha256=hashlib.sha256(z.read_bytes()).hexdigest()))
out=dict(admission=a,admission_exit=r.returncode,imports=imports,seed_bytes=sum(x['size'] for x in imports),workspace=str(b),cache={C!r})
(b/'NJV_SEED.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=script,text=True,capture_output=True)
(E/'NJV_seed_transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
if r.returncode: (E/'NJV_seed_refusal.json').write_text(r.stdout);print('NJV seed refused exit',r.returncode);raise SystemExit(r.returncode)
x=json.loads(r.stdout);(E/'NJV_SEED.json').write_text(json.dumps(x,indent=2)+'\n');print('NJV seed:',len(x['imports']),'files,',x['seed_bytes'],'bytes; admission exit 0 allowed true')
