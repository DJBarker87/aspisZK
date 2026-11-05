"""Admitted copy of final retained parser exports into the NHF private seed."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-candidate-prepare-20261106';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHF_seed_20261106/NGV_exports'
code=f'''from pathlib import Path
import subprocess,json,sys,shutil,hashlib
b=Path({B!r});p=b/'NHF_PARSER_SEED-admission.json'
with (b/'NHF_PARSER_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
if r.returncode!=0 or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
root=b.parent/'codex-cx-slice-d-parser2-cache-20261104/NGV_exports_20261105';c=Path({C!r});c.mkdir(exist_ok=True);out=[]
for p in sorted(root.rglob('*')):
 if not p.is_file():continue
 q=c/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():shutil.copyfile(p,q)
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 out.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
print('NHF_PARSER_SEED '+json.dumps(dict(files=out,total_bytes=sum(x['bytes'] for x in out))))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 (E/f'NHF_PARSER_SEED-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 if r.returncode==78 and retry<10:time.sleep(180);continue
 if r.returncode==79 and retry==0:time.sleep(30);continue
 raise RuntimeError(r.stdout+r.stderr)
else:raise RuntimeError('admission exhausted')
seed=json.loads(next(x.removeprefix('NHF_PARSER_SEED ') for x in r.stdout.splitlines() if x.startswith('NHF_PARSER_SEED ')));(E/'NHF_PARSER_SEED.json').write_text(json.dumps(seed,indent=1)+'\n')
p=E/'NHF_PATHS.json';paths=json.loads(p.read_text());paths.insert(2,C);p.write_text(json.dumps(paths,indent=1)+'\n');print(seed['total_bytes'])
