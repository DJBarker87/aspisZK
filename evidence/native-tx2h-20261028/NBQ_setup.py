from pathlib import Path
import subprocess,shlex,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2h-20261028'
code='''from pathlib import Path
import subprocess,json,sys
b=Path(%r);b.mkdir(exist_ok=True)
with (b/'NBQ_START-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NBQ_START-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
print(json.dumps(dict(exit=r.returncode,receipt=(b/'NBQ_START-reservation.json').read_text() if (b/'NBQ_START-reservation.json').exists() else None,log=(b/'NBQ_START-barrier.log').read_text())))
'''%B
for n in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
 (E/f'NBQ_START-transport-{n}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr)))
 if r.returncode==255:
  if n<10:time.sleep(60);continue
  raise SystemExit('transport exhausted')
 assert r.returncode==0,r.stderr
 z=json.loads(r.stdout);ad=json.loads(z['receipt']) if z['receipt'] else None
 if ad and z['exit']==0 and ad.get('allowed') is True:break
 if not ad and n==0:time.sleep(30);continue
 if ad and (z['exit']==78 or ad.get('allowed') is False) and n<10:time.sleep(180);continue
 raise SystemExit('STOP admission')
code='''from pathlib import Path
import hashlib,shutil,json
base=Path('/home/dombarker/project-offloads');b=base/'codex-cx-native-tx2h-20261028';c=base/'codex-cx-tx2mid-cache-20261028';old=base/'codex-cx-leaf-cache-20261027'
assert not c.exists(),'inspect existing cache rather than reseeding'
c.mkdir()
manifest={}
for p in old.rglob('*'):
 if p.is_file():
  q=c/p.relative_to(old);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==hashlib.sha256(q.read_bytes()).hexdigest()
  manifest[str(q)]=dict(imported_from=str(p),sha256=h,bytes=q.stat().st_size)
(b/'NBQ_CACHE_START.json').write_text(json.dumps(manifest,indent=2))
root=base/'codex-cx-sound-int2-20261025'/'objects'
pins={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in [root/'Aeneas.olean']+list((root/'Aeneas').rglob('*.olean'))}
(b/'NBQ_LIBRARY_START.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(dict(cache=manifest,library=pins)))
'''
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/'NBQ_SETUP-transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stderr
x=json.loads(r.stdout)
for k,n in [('cache','NBQ_CACHE_START.json'),('library','NBQ_LIBRARY_START.json')]: (E/n).write_text(json.dumps(x[k],indent=2)+'\n')
