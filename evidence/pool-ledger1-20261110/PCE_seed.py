"""Copy only the selected import closure into this job's cache; hashes retained."""
from pathlib import Path
import json,subprocess,lzma,base64
E=Path(__file__).resolve().parent
payload=base64.b64encode(lzma.compress((E/'PCE_SEED_REQUEST.json').read_bytes())).decode()
code=r'''
from pathlib import Path
import json,hashlib,lzma,base64,shutil,subprocess,sys
B=Path('/home/dombarker/project-offloads/codex-pc-pool-ledger1-20261110');C=Path('/home/dombarker/project-offloads/codex-pc-pool-ledger1-cache-20261110');B.mkdir(exist_ok=True);C.mkdir(exist_ok=True)
with (B/'PCE_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'PCE_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=B/'PCE_SETUP-reservation.json';ad=json.loads(p.read_text()) if p.exists() else None
if r.returncode!=0 or not ad or ad.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,admission=ad)));sys.exit(r.returncode or 78)
assert shutil.disk_usage(B).free>=40_000_000_000
x=json.loads(lzma.decompress(base64.b64decode(PAYLOAD)));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();selected={v['relative']:v for v in x['files']}
# Seed fallback directories contain retained PCA/NIZ objects. Only select missing modules.
for m in x['closure']:
 if m=='PCE_COMBINED_IMPORT':continue
 stem=m.replace('.','/');rel=stem+'.olean'
 if rel in selected:continue
 candidates=[Path(v['target']) for v in x['pca_seed']['files'] if str(v['target']).endswith('/'+rel)]+[Path(d)/rel for d in x['extra_search']]
 p=next((p for p in candidates if p.is_file()),None);assert p is not None,('missing module',m)
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():
   rr=stem+'.ir' if z.suffix=='.ir' else rel+str(z)[len(str(p)):]
   selected[rr]=dict(module=m,path=str(z),relative=rr,sha256=sha(z),bytes=z.stat().st_size)
imports={}
for rel,v in selected.items():
 p=Path(v['path']);assert sha(p)==v['sha256'],str(p)
 q=C/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==v['sha256'],rel
 else:shutil.copyfile(p,q)
 assert sha(q)==v['sha256'] and p.stat().st_ino!=q.stat().st_ino
 imports[rel]=dict(source=str(p),sha256=v['sha256'],bytes=q.stat().st_size,module=v['module'])
for sub in ['PCE_objects','PCE_generated','PCE_native','PCE_tmp']:(B/sub).mkdir(exist_ok=True)
W=B.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:shutil.copyfile(W/n,B/n)
X=B.parent/'codex-pc-helpers1-cache-20261110/PCB_exports_20261110/PCB_native'
for old,new in [('PCB_WALKER.c','PCE_WALKER.c'),('PCB_MemoryLimit.c','PCE_MemoryLimit.c')]:shutil.copyfile(X/old,B/'PCE_native'/new)
(B/'PCE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(imports).encode()))
print(json.dumps(dict(exit=0,admission=ad,files=len(imports),bytes=sum(v['bytes'] for v in imports.values()),manifest=base64.b64encode((B/'PCE_IMPORTS.json.xz').read_bytes()).decode(),disk=shutil.disk_usage(B)._asdict(),tools={str(p):sha(p) for p in [B/'S2W_run_host.py',B/'S2W_lean_host.py',B/'PCE_native/PCE_WALKER.c',B/'PCE_native/PCE_MemoryLimit.c']})))
'''.replace('PAYLOAD',repr(payload))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'PCE_SETUP.log').write_text(r.stderr)
assert r.returncode==0,(r.returncode,r.stdout[-1000:],r.stderr[-1000:])
x=json.loads(r.stdout);(E/'PCE_IMPORTS.json.xz').write_bytes(base64.b64decode(x.pop('manifest')));(E/'PCE_SETUP.json').write_text(json.dumps(x,indent=1)+'\n')
print('Copied and verified '+str(x['files'])+' import files; host free '+str(x['disk']['free'])+' bytes.')
