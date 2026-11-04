from pathlib import Path
import subprocess,json,hashlib,lzma
E=Path(__file__).resolve().parent
x=json.loads((E/'NFF_NFB_CACHE_INPUT.json').read_text());archive=json.loads(lzma.decompress((E/'NFF_NFB_IMPORT.json.xz').read_bytes()))
assert x['revision']==archive['revision']
source_hashes={v['sha256'] for v in archive['blobs'].values()}
assert all(r['source_sha256'] in source_hashes for r in x['exports']['exports'])
code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul7-20261029')
with (B/'NFF_NFB_COPY-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NFF_NFB_COPY-admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((B/'NFF_NFB_COPY-admission.json').read_text())
if r.returncode!=0 or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,admission=a)));sys.exit(78)
x=json.loads(PAYLOAD)
S=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose5-cache-20261029')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul7-cache-20261029/NFF_NFB_support')
records=[]
items=[(v['selected_path'],v['selected_sha256']) for v in x['cache'].values()]
items += [(v['destination'],v['sha256']) for v in x['exports']['exports']]
for name,h in items:
 p=Path(name);rel=p.relative_to(S);q=C/rel
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h,(name,'peer cache hash drift')
 q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 else:shutil.copyfile(p,q)
 records.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
 for z in [Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  dest=C/z.relative_to(S);digest=hashlib.sha256(z.read_bytes()).hexdigest()
  dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists():assert hashlib.sha256(dest.read_bytes()).hexdigest()==digest
  else:shutil.copyfile(z,dest)
  records.append(dict(source=str(z),destination=str(dest),sha256=digest,bytes=dest.stat().st_size))
print(json.dumps(dict(exit=0,admission=a,revision=x['revision'],imports=records)))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NFF_NFB_COPY-transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stdout+r.stderr
out=json.loads(r.stdout);(E/'NFF_NFB_OBJECT_IMPORTS.json').write_text(json.dumps(out));print('pinned peer objects/sidecars copied',len(out['imports']))
