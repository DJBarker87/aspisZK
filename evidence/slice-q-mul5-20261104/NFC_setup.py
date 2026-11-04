from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import shutil,hashlib,json,subprocess,sys
P=Path('/home/dombarker/project-offloads'); B=P/'codex-cx-slice-q-mul5-20261029'; C=P/'codex-cx-slice-q-mul5-cache-20261029'
B.mkdir(exist_ok=True);C.mkdir(exist_ok=True)
with (B/'NFC_setup_barrier.log').open('w') as f:r=subprocess.run(['python3',str(P/'codex-cx-s2h-20261023/S2H_reservation.py'),str(B/'NFC_setup_reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((B/'NFC_setup_reservation.json').read_text());print(json.dumps(dict(admission=a,exit=r.returncode)),flush=True)
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(78)
entries=[]
seeds=['codex-cx-slice-q-mul4-cache-20261029','codex-cx-leaf-cache-20261027','codex-cx-cpilot-cache-20261028','codex-cx-slice-q-mul3-cache-20261029','codex-cx-slice-q-mul2-cache-20261029','codex-cx-slice-q-mul-cache-20261029','codex-cx-front1-cache-20261028','codex-cx-slice-q-leaves-cache-20261029']
for seed in seeds:
 for p in sorted((P/seed).rglob('*')):
  if not p.is_file() or not any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  n=p.relative_to(P/seed);q=C/n
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
  h=hashlib.sha256(q.read_bytes()).hexdigest();assert h==hashlib.sha256(p.read_bytes()).hexdigest()
  entries.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 p=P/'codex-cx-slice-q-mul4-20261029'/n;q=B/n
 if not q.exists():shutil.copyfile(p,q)
for n in ['NFC_objects','NFC_tmp','NFC_native','NFC_generated']:(B/n).mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=P/'codex-cx-slice-q-mul4-20261029/NFA_native'/n;q=B/'NFC_native'/n;shutil.copyfile(p,q)
 entries.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(dict(cache=str(C),imports=entries)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NFC_SETUP_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
(E/'NFC_SETUP.log').write_text(r.stdout)
assert r.returncode==0,r.stderr+r.stdout[:1000]
(E/'NFC_CACHE_IMPORTS.json').write_text(r.stdout.splitlines()[-1])
print('copied',len(json.loads(r.stdout.splitlines()[-1])['imports']),'objects/sidecars')
