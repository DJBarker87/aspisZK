from pathlib import Path
import json,subprocess,lzma,time
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-rowspec-canon-20261110'
roots=json.loads((E/'NMG_SEED_PATHS.json').read_text())
code='''from pathlib import Path
import json,subprocess,sys,hashlib,shutil,lzma
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NMG_seed-admission.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NMG_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NMG_seed-admission.json'
if not p.exists():sys.exit(79)
a=json.loads(p.read_text())
if r.returncode or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
assert shutil.disk_usage(b).free>=40_000_000_000
cache=b/'NMG_seed';cache.mkdir(exist_ok=True);selected={};manifest=[]
for root in roots[:5]:
 p=Path(root)
 assert p.is_dir(),root
 for z in sorted(p.rglob('*')):
  if not z.is_file() or not any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  rel=str(z.relative_to(p))
  if rel in selected:continue
  selected[rel]=z
assert sum(z.stat().st_size for z in selected.values())<1_000_000_000
for rel,z in selected.items():
 q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True)
 sha=hashlib.sha256(z.read_bytes()).hexdigest()
 if not q.exists():shutil.copy2(z,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==sha,str(q)
 manifest.append(dict(source=str(z),relative=rel,path=str(q),sha256=sha,bytes=q.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
for n in ['NMG_objects','NMG_generated','NMG_tmp']: (b/n).mkdir(exist_ok=True)
for n in ['NHS_PreparedPacket','NHL_OpeningPacket','NLR_Prepare','NLR_PrepareReachedDomain','NHS_CallerWidths','NHS_PrepareFields','NLU_RowSpec136']:
 candidates=[]
 for folder in [Path('/home/dombarker/project-offloads/codex-cx-tx1-observed-20261110/NLR_generated'),Path('/home/dombarker/project-offloads/codex-cx-tx1-finish2-20261110/NLU_generated')]:
  p=folder/(n+'.lean')
  if p.exists():candidates.append(p)
 if not candidates:
  for root in roots:
   p=Path(root).parent
   for folder in ['NHS_generated','NLU_generated','NLR_generated','NHS_sources']:
    z=p/folder/(n+'.lean')
    if z.exists():candidates.append(z);break
   if candidates:break
 if candidates:
  q=b/'NMG_readonly_sources'/ (n+'.lean.txt');q.parent.mkdir(exist_ok=True);shutil.copy2(candidates[0],q)
(b/'NMG_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(dict(files=manifest,admission=a,exit=r.returncode,disk=shutil.disk_usage(b)._asdict())).encode()))
print(json.dumps(dict(files=len(manifest),bytes=sum(r['bytes'] for r in manifest),disk=shutil.disk_usage(b)._asdict())))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nroots='+repr(roots)+'\n'+code,text=True,capture_output=True)
 (E/f'NMG_seed-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:break
 if r.returncode in [78,79,255] and retry<10:time.sleep(180 if r.returncode==78 else 30 if r.returncode==79 else 60);continue
 raise RuntimeError(r.stderr+r.stdout[-1000:])
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat '+B+'/NMG_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0;(E/'NMG_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
print('NMG seed copied and hashes checked')
