"""Prepare small owned host scratch from immutable retained inputs; no builds."""
from pathlib import Path
import subprocess,json,hashlib,time,lzma,sys,base64
E=Path(__file__).resolve().parent;I=E.parent/'pool-b3-20261106'
B='/home/dombarker/project-offloads/codex-cx-pool-b4-20261107';H='dombarker@100.108.41.90'
# Lane-owned validation drivers: preserve checks and caps; only relocate/prefix.
for old in ['NHP_kani_run.py','NHP_kani_gate.py','NHP_run.py']:
 text=(I/old).read_text().replace('NHP','NIE').replace('pool-b3-20261106','pool-b4-20261107')
 for name in ['INCLUDES.json','FROZEN_GRAPH.json','FROZEN_INPUT.json.sha256','FROZEN_SHA256.json','KMX_copy_stubs.patch']:
  text=text.replace("E/'NIE_"+name+"'", "I/'NHP_"+name+"'")
 # Every native input remains frozen plus exact patches; add owned module scan.
 if old=='NHP_kani_gate.py':text=text.replace("*S.rglob('NIE_*.rs')", "*S.rglob('NIE_*.rs')")
 # All stdout from compiler/prover remains on disk; even exception diagnostics suppressed by client queue.
 text=text.replace("E=Path(__file__).resolve().parent;", "E=Path(__file__).resolve().parent;I=E.parent/'pool-b3-20261106';",1)
 if old=='NHP_run.py':
  text=text.replace("C+'/NHC_exports_20261105'", "C+'/NHP_exports_20261106',C+'/NHP_native_exports_20261106',C+'/NHC_exports_20261105'")
  text=text.replace("(b/'NIE_CACHE_IMPORTS.json.xz')", "(b/'NIE_CACHE_IMPORTS.json.xz')")
 (E/old.replace('NHP','NIE')).write_text(text)
text=(I/'NHP_frozen_identity.py').read_text().replace("E=Path(__file__).resolve().parent", "E=Path(__file__).resolve().parent.parent/'pool-b3-20261106'")
(E/'NIE_frozen_identity.py').write_text(text)
# Retained native seed is consumed once by hash, not duplicated in the repo.
p=I/'NHP_NATIVE_SEED.json.xz';payload=p.read_bytes();seed_sha=hashlib.sha256(payload).hexdigest()
imports=[]
for n in ['NHP_NATIVE_SEED.json.xz','NHP_NATIVE_SEED.json.sha256','NHP_FROZEN_GRAPH.json','NHP_INCLUDES.json','NHP_KMX_copy_stubs.patch','NHP_frozen_identity.py']:
 q=I/n;imports.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
(E/'NIE_INPUT_PINS.json').write_text(json.dumps(imports,indent=2)+'\n')
code='''from pathlib import Path
import subprocess,json,hashlib,lzma,base64,shutil,sys
b=Path(B);b.mkdir(exist_ok=True)
q=b/'NIE_SEED-reservation.json'
with (b/'NIE_SEED-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads(q.read_text());print(json.dumps(dict(admission=ad,exit=r.returncode)),flush=True)
if r.returncode or ad.get('allowed') is not True:sys.exit(78)
seed=base64.b64decode(seed_base64)
assert hashlib.sha256(seed).hexdigest()==seed_sha
files=json.loads(lzma.decompress(seed));s=b/'NIE_src';s.mkdir(exist_ok=True);total=0
for n,v in files.items():
 raw=base64.b64decode(v);dest=s/n;dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():assert dest.read_bytes()==raw,n
 else:dest.write_bytes(raw)
 total+=len(raw)
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2(w/n,b/n);assert (w/n).read_bytes()==(b/n).read_bytes()
for n in ['NIE_tmp','NIE_objects','NIE_native']:(b/n).mkdir(exist_ok=True)
c=Path('/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104');rows=[]
x=json.loads(Path('/home/dombarker/project-offloads/codex-cx-pool-b3-20261106/NHP_EXPORT.json').read_text())
for row in x['exports']:
 p=Path(row['path']);assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 rows.append(dict(row,copied=False))
raw=json.dumps(dict(imports=rows,seed_bytes=0,reused_bytes=sum(r['bytes'] for r in rows))).encode()
(b/'NIE_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(b/'NIE_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
(b/'NIE_SEED.json').write_text(json.dumps(dict(native_files=len(files),native_seed_bytes=total,objects_copied=0,exports=rows,cache_retained=str(c))))
print(json.dumps(dict(native_seed_bytes=total,exports=len(rows),object_bytes_copied=0)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nseed_sha='+repr(seed_sha)+'\nseed_base64='+repr(base64.b64encode(payload).decode())+'\n'+code,text=True,capture_output=True)
 (E/f'NIE_SEED-repair-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:print(r.stdout);break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 if r.returncode==78 and retry<10:time.sleep(180);continue
 print(json.dumps(dict(exit=r.returncode,details='NIE_SEED-'+str(retry)+'.log')));sys.exit(r.returncode)
else:raise SystemExit('Seed admission/transport exhausted')
