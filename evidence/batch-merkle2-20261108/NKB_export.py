"""Retain verified proof objects, then remove only this job's disposable compiled outputs."""
from pathlib import Path
import json,subprocess,sys
sys.dont_write_bytecode=True
import NKB_resolve as R
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-batch-merkle2-20261108';D='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKB_20261108/NKB_exports_final_20261108'
inv=json.loads((E/'NKB_PROOF_INVENTORY.json').read_text());pins=json.loads(R.read('NKB_AUDIT2_BINARY_PINS.json'))
code=f'''from pathlib import Path
import json,shutil,hashlib,time
b=Path({B!r});d=Path({D!r});d.mkdir(exist_ok=False)
inv=json.loads({json.dumps(inv)!r});binary_pins=json.loads({json.dumps(pins)!r})
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1<<20),b''):h.update(block)
 return h.hexdigest()
rows=[]
for name in list(inv['modules'])+['NKB_COMBINED_IMPORT']:
 if name in inv['modules']:assert sha(b/'NKB_lean'/(name+'.lean'))==inv['modules'][name]['source_sha256']
 p=b/'NKB_objects'/(name+'.olean');assert p.is_file(),name
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():
   dest=d/q.name;shutil.copy2(q,dest);h=sha(q);assert sha(dest)==h
   rows.append(dict(module=name,path=str(dest),bytes=q.stat().st_size,sha256=h))
for n,h in binary_pins.items():assert sha(b/n)==h
before=shutil.disk_usage(b).free;removed=[]
for p in [b/'NKB_target',b/'NKB_objects']:
 if p.exists():shutil.rmtree(p);removed.append(str(p))
for n in binary_pins:
 p=b/n;p.unlink();removed.append(str(p))
# TMPDIR is this owned workspace. Never sweep shared /tmp or other workers' trees.
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in b.glob(pattern):
  if p.is_file():p.unlink();removed.append(str(p))
print(json.dumps(dict(time=time.time(),retained_export=str(d),objects=rows,bytes=sum(x['bytes'] for x in rows),removed_disposable_outputs=removed,free_before=before,free_after=shutil.disk_usage(b).free,retained_cache_deleted=False),indent=2))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NKB_EXPORT.json').write_text(r.stdout)
env=json.loads((E/'NKB_ENV.json').read_text());env['LEAN_PATH']=':'.join([D]+env['LEAN_PATH'].split(':')[1:]);(E/'NKB_ENV_FINAL.json').write_text(json.dumps(env,indent=2)+'\n')
x=json.loads(r.stdout);print('Final proof export verified:',len(x['objects']),'objects /',x['bytes'],'bytes; only owned compiled scratch removed')
