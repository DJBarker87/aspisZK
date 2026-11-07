from pathlib import Path
import json,lzma,subprocess,hashlib,base64
E=Path(__file__).resolve().parent
imports=json.loads(lzma.decompress((E.parent/'pool-ledger1-20261110/PCE_IMPORTS.json.xz').read_bytes()))
for rel,v in imports.items():v['source']='/home/dombarker/project-offloads/codex-pc-pool-ledger1-cache-20261110/'+rel
exports=json.loads((E.parent/'pool-ledger1-20261110/PCE_EXPORT_MANIFEST.json').read_text())
for v in exports['files']:
 rel=v['path'].split('/PCE_exports_20261110/')[1];imports[rel]=dict(source=v['path'],sha256=v['sha256'],bytes=v['bytes'])
payload=base64.b64encode(lzma.compress(json.dumps(dict(imports=imports,inputs=json.loads(lzma.decompress((E/'PCG_FROZEN_INPUTS.json.xz').read_bytes())))).encode())).decode()
code=r'''from pathlib import Path
import json,hashlib,lzma,base64,shutil,subprocess,sys
B=Path('/home/dombarker/project-offloads/codex-pc-helpers2-20261110');C=B.parent/'codex-pc-helpers2-cache-20261110';B.mkdir(exist_ok=True);C.mkdir(exist_ok=True)
assert shutil.disk_usage(B).free>=40_000_000_000
x=json.loads(lzma.decompress(base64.b64decode(PAYLOAD)));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,v in x['imports'].items():
 p=Path(v['source']);assert sha(p)==v['sha256'],str(p)
 q=C/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==v['sha256'],rel
 else:shutil.copyfile(p,q)
 assert p.stat().st_ino!=q.stat().st_ino
for n in ['PCG_objects','PCG_generated','PCG_native','PCG_tmp']:(B/n).mkdir(exist_ok=True)
W=B.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:shutil.copyfile(W/n,B/n)
S=B/'PCG_src'
if not S.exists():shutil.copytree(B.parent/'codex-pc-helpers1-20261110/PCB_src',S,ignore=shutil.ignore_patterns('target','__pycache__','.git'))
for p in S.rglob('PCB_*.rs'):p.unlink()
for n,s in x['inputs'].items():p=S/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(s))
pins={n:sha(S/n) for n in x['inputs']};(B/'PCG_SOURCE_PINS.json').write_text(json.dumps(pins))
(B/'PCG_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x['imports']).encode()))
print(json.dumps(dict(files=len(x['imports']),bytes=sum(v['bytes'] for v in x['imports'].values()),frozen_files=len(pins),disk_free=shutil.disk_usage(B).free)))
'''.replace('PAYLOAD',repr(payload))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'PCG_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
(E/'PCG_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(imports).encode()))
print('PCG seed exit0; copied and pinned coherent imports and frozen scratch inputs')
