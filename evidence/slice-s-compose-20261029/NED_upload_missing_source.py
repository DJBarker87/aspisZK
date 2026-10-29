"""Repair an own scratch input omission using immutable frozen Git bytes."""
from pathlib import Path
import subprocess,json,hashlib,time,posixpath,re,base64
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose-20261029';H='dombarker@100.108.41.90';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
initial=json.loads((E/'NED_RUST_SOURCE_PINS.json').read_text())['files']
known=set(initial)|set(json.loads((E/'NED_RUST_SHA256.json').read_text()))
files={};pending=[p for p in known if p.endswith('.rs')];visited=set();unresolved=[]
while pending:
 p=pending.pop()
 if p in visited:continue
 visited.add(p)
 raw=subprocess.check_output(['git','show',rev+':'+p],stderr=subprocess.DEVNULL).decode() if not p.endswith('/NED_controls.rs') and p!='KMX_stubs.rs' and p!='KMX_native.rs' else ''
 for m in re.finditer(r'(?:#\[\s*path\s*=\s*|include(?:_str|_bytes)?!\(\s*)"([^"\n]+)"',raw):
  n=posixpath.normpath(posixpath.dirname(p)+'/'+m[1])
  if n in known or n in files:continue
  data=subprocess.run(['git','show',rev+':'+n],capture_output=True)
  if data.returncode:unresolved.append(dict(source=p,literal=m[1],candidate=n));continue
  files[n]=base64.b64encode(data.stdout).decode()
  if n.endswith('.rs'):pending.append(n)
history=E/'NED_SOURCE_REPAIRS.jsonl'
if not history.exists() and (E/'NED_SOURCE_REPAIR.json').exists():history.write_text((E/'NED_SOURCE_REPAIR.json').read_text().replace('\n','')+'\n')
event=1+len(history.read_text().splitlines()) if history.exists() else 1
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});log=b/'NED_SOURCE_REPAIR-barrier.log'
with log.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NED_SOURCE_REPAIR-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text());sys.exit(r.returncode)
'''
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True);(E/f'NED_SOURCE_REPAIR_{event}-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==255:
  if retry<10:time.sleep(60);continue
  raise SystemExit('transport exhausted')
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except Exception:
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation JSON missing')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise SystemExit('admission refused')
code=f'''from pathlib import Path
import json,hashlib,base64
b=Path({B!r});s=b/'NED_src';files=json.loads({json.dumps(files)!r});pins=json.loads((b/'NED_RUST_SHA256.json').read_text())
for n,v in files.items():
 p=s/n;data=base64.b64decode(v);assert not p.exists() or p.read_bytes()==data,n
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NED_RUST_SHA256.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
(E/'NED_RUST_SHA256.json').write_text(r.stdout)
(E/'NED_SOURCE_REPAIR.json').write_text(json.dumps(dict(reason='K002 codegen stopped before verification: frozen non-Cargo include closure omitted from own source archive',revision=rev,files={p:dict(sha256=hashlib.sha256(base64.b64decode(v)).hexdigest(),bytes=len(base64.b64decode(v))) for p,v in files.items()},admission=ad,new_solver_runs=0,unresolved_literal_paths=unresolved),indent=1)+'\n')
with history.open('a') as f:f.write((E/'NED_SOURCE_REPAIR.json').read_text().replace('\n','')+'\n')
print('added',len(files),'unchanged frozen compile inputs;',len(unresolved),'unresolved optional literal paths recorded')
