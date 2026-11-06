from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-batch-merkle3-20261108'
paths=json.loads(Path('evidence/ledger18-20261108/NKH_PATHS.json').read_text())
nkb=json.loads(Path('evidence/batch-merkle2-20261108/NKB_ENV_FINAL.json').read_text())
code='''from pathlib import Path
import shutil,json,hashlib,subprocess,sys
b=Path(B);b.mkdir(exist_ok=True)
assert shutil.disk_usage(b).free>=40000000000
p=b/'NKL_SEED-admission.json'
with (b/'NKL_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(p.read_text()) if p.exists() else {}; assert r.returncode==0 and a.get('allowed') is True, ('ADMISSION',r.returncode,a)
records=[]; roots=[]
for src,label in [('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKB_20261108/NKB_exports_final_20261108','NKB'),('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKH_20261108/NKH_exports_20261108','NKH')]:
 target=b/('NKL_seed/'+label);target.mkdir(parents=True,exist_ok=True); roots.append(str(target))
 for s in sorted(Path(src).rglob('*')):
  if not s.is_file():continue
  d=target/s.relative_to(src);d.parent.mkdir(parents=True,exist_ok=True)
  assert not d.exists()
  shutil.copy2(s,d);h=hashlib.sha256(s.read_bytes()).hexdigest();assert hashlib.sha256(d.read_bytes()).hexdigest()==h
  records.append(dict(source=str(s),destination=str(d),bytes=d.stat().st_size,sha256=h))
roots=list(dict.fromkeys([str(b/'NKL_objects')]+roots+paths+nkb['LEAN_PATH'].split(':')[1:]))
(b/'NKL_objects').mkdir(exist_ok=True)
env={**nkb,'TMPDIR':B,'CARGO_TARGET_DIR':B+'/NKL_target','LEAN_PATH':':'.join(roots)}
(b/'NKL_ENV.json').write_text(json.dumps(env,indent=2)+'\\n')
shutil.copy2('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/S2W_run_host.py',b/'S2W_run_host.py')
receipt=dict(files=records,total_bytes=sum(x['bytes'] for x in records),free_bytes=shutil.disk_usage(b).free,admission=a,admission_exit=r.returncode,env=env)
(b/'NKL_SEED.json').write_text(json.dumps(receipt,indent=2)+'\\n')
print(json.dumps(receipt))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\npaths='+repr(paths)+'\nnkb='+repr(nkb)+'\n'+code,text=True,capture_output=True)
(E/'NKL_SEED.log').write_text(r.stderr)
assert r.returncode==0,(r.returncode,r.stderr,r.stdout[-1500:])
x=json.loads(r.stdout);(E/'NKL_SEED.json').write_text(json.dumps(x,indent=2)+'\n');(E/'NKL_ENV.json').write_text(json.dumps(x['env'],indent=2)+'\n')
print(json.dumps(dict(seed_bytes=x['total_bytes'],free_bytes=x['free_bytes'],admitted=True)))
