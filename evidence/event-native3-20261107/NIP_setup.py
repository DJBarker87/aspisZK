from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-event-native3-20261107'
C='/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIP_20261107'
code=f'''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path({B!r});c=Path({C!r});b.mkdir(exist_ok=True)
with (b/'NIP_seed-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NIP_seed-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NIP_seed-reservation.json'
ad=json.loads(p.read_text()) if p.exists() else None
receipt=dict(exit=r.returncode,reservation=ad)
print(json.dumps(dict(admission=receipt)),flush=True)
if r.returncode!=0 or not ad or ad.get('allowed') is not True:sys.exit(78)
c.mkdir(exist_ok=True)
roots=['/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIN_20261107/NIN_exports_20261107','/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIF_20261107/NIF_exports_final_20261107','/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIF_20261107/NGK_exports_20261105']
rows=[]
for root in roots:
 for p in sorted(Path(root).rglob('*')):
  if not p.is_file():continue
  q=c/Path(root).name/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  digest=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==digest
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=digest))
for n in ['S2W_run_host.py','S2W_lean_host.py']:
 p=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')/n;q=b/n
 if q.exists():assert p.read_bytes()==q.read_bytes()
 else:shutil.copy2(p,q)
manifest=dict(files=rows,seed_bytes=sum(x['bytes'] for x in rows),seed_count=len(rows))
(b/'NIP_SEED.json').write_text(json.dumps(manifest,indent=1)+'\\n')
print(json.dumps(dict(seed=manifest)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NIP_seed-transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
for line in r.stdout.splitlines():
 x=json.loads(line)
 for k,v in x.items():(E/('NIP_'+('seed-admission' if k=='admission' else 'SEED')+'.json')).write_text(json.dumps(v,indent=1)+'\n')
assert r.returncode==0,r.stdout+r.stderr
s=json.loads((E/'NIP_SEED.json').read_text()); print(json.dumps({k:s[k] for k in ['seed_count','seed_bytes']}))
