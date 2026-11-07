from NNC_transport import *
import hashlib,lzma
branch='codex/cx-stage-wrap-20261107'
rev=subprocess.check_output(['git','rev-parse',branch],text=True).strip()
sources={}
for n in ['NMV_RslLaws','NMV_RslSnapshots']:
 raw=subprocess.check_output(['git','show',rev+':evidence/stage-wrap-20261111/'+n+'.lean'])
 h=hashlib.sha256(raw).hexdigest();p=E/'NNC_INPUTS'/(h+'.xz');p.write_bytes(lzma.compress(raw));sources[n]=dict(sha256=h,archive=str(p.relative_to(E)),revision=rev)
admission('NNC_S003')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});src=b.parent/'codex-cx-stage-wrap-20261111';out=b/'NNC_seed/NMV';rows=[]
expected=json.loads({json.dumps(sources)!r})
for p in sorted((src/'NMV_objects').glob('*')):
 if not p.is_file():continue
 if not (p.name.startswith('RSL_') or p.stem in expected):continue
 q=out/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if p.stem in expected:
  raw=(src/'NMV_generated'/(p.stem+'.lean')).read_bytes()
  assert hashlib.sha256(raw).hexdigest()==expected[p.stem]['sha256']
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:shutil.copy2(p,q)
 rows.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
assert (out/'RSL_TX1_330.olean').is_file()
print(json.dumps(dict(files=rows,sources=expected)))
''');assert r.returncode==0,r.stderr
(E/'NNC_SUPPORT_SEED.json').write_text(r.stdout)
p=E/'NNC_ENV.json';x=json.loads(p.read_text());paths=x['LEAN_PATH'].split(':');paths.insert(1,B+'/NNC_seed/NMV');x['LEAN_PATH']=':'.join(dict.fromkeys(paths));p.write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(files=len(json.loads(r.stdout)['files']))))
