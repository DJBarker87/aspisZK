from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
src='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJZ_exports_20261108'
dst='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKB_20261108/NKB_NJZ_seed'
code=f'''from pathlib import Path
import shutil,hashlib,json
s=Path({src!r}); d=Path({dst!r});d.mkdir(exist_ok=True)
r=[]
for p in sorted(s.rglob('*')):
 if p.is_file():
  q=d/p.relative_to(s);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  r.append(dict(source=str(p),copy=str(q),bytes=p.stat().st_size,sha256=h))
print(json.dumps(dict(files=r,bytes=sum(x['bytes'] for x in r)),indent=2))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NKB_NJZ_SEED.json').write_text(r.stdout)
x=json.loads((E/'NKB_ENV.json').read_text());old=x['LEAN_PATH'].split(':');j=json.loads((E/'NKB_NJZ_INPUTS.json').read_text());paths=json.loads(next(f['text'] for f in j['files'] if f['path'].endswith('NJZ_PATHS.json')))
x['LEAN_PATH']=':'.join(dict.fromkeys([old[0],dst]+old[1:]+paths));(E/'NKB_ENV.json').write_text(json.dumps(x,indent=2)+'\n')
print('NJZ seed copied and hashed:',json.loads(r.stdout)['bytes'],'bytes')
