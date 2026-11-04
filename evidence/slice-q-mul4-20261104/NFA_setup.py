from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import shutil,hashlib,json
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-q-mul4-20261029';C=P/'codex-cx-slice-q-mul4-cache-20261029'
B.mkdir(exist_ok=True);C.mkdir(exist_ok=True)
entries=[]
seeds=['codex-cx-slice-q-mul3-cache-20261029','codex-cx-leaf-cache-20261027','codex-cx-cpilot-cache-20261028','codex-cx-slice-q-mul2-cache-20261029','codex-cx-slice-q-mul-cache-20261029','codex-cx-front1-cache-20261028','codex-cx-slice-q-leaves-cache-20261029']
for seed in seeds:
 for p in sorted((P/seed).rglob('*')):
  if not p.is_file() or not any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  n=p.relative_to(P/seed);q=C/n
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
  h=hashlib.sha256(q.read_bytes()).hexdigest();assert h==hashlib.sha256(p.read_bytes()).hexdigest()
  entries.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 p=P/'codex-cx-slice-q-mul3-20261029'/n;q=B/n
 assert not q.exists();shutil.copyfile(p,q)
(B/'NFA_objects').mkdir(exist_ok=True);(B/'NFA_tmp').mkdir(exist_ok=True)
print(json.dumps(dict(cache=str(C),imports=entries,priority=['NEV_exports_20261104','SInt2','NEI_exports_20261103','NEG_results_20261101','NEB_exports_20261029','.'])))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NFA_SETUP_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stderr
(E/'NFA_CACHE_IMPORTS.json').write_text(r.stdout)
print('copied',len(json.loads(r.stdout)['imports']),'objects/sidecars')
