from pathlib import Path
import json,subprocess,sys,time,hashlib,base64,zlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-tx2m-20261028'
mode=sys.argv[1]
def rpc(code,submitted=False):
 for trial in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
  with (E/'NCD_BATCH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(mode=mode,trial=trial,submitted=submitted,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if trial<10:time.sleep(60)
 raise SystemExit('STOP persistent transport failure')
if mode=='submit':
 assert not (E/'NCD_BATCH_ACTIVE').exists() and not (E/'NCD_NATIVE_BATCH_ACTIVE').exists()
 payload=dict(plan=json.loads((E/'NCD_focus_plan.json').read_text()),runner=(E/'NCD_focus_host.py').read_text(),launchers=json.loads((E/'NCD_LAUNCHER_INPUTS.json').read_text()))
 blob=base64.b64encode(zlib.compress(json.dumps(payload).encode())).decode()
 code=f'''from pathlib import Path
import subprocess,json,zlib,base64,sys,hashlib
b=Path({B!r});p=b/'NCD_focus_initial_reservation.json'
with (b/'NCD_focus_initial_barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
a=json.loads(p.read_text());print(json.dumps(a),flush=True)
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(r.returncode if r.returncode else 78)
x=json.loads(zlib.decompress(base64.b64decode({blob!r})))
assert not (b/'NCD_focus_submitted.json').exists(),'never submit twice'
for n in ['S2W_lean_host.py','S2W_run_host.py']:assert (b/n).read_text()==x['launchers'][n]
for row in x['plan']['rows']:
 p=b/row['cfg']['sources'][0];p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists() and p.read_text()!=row['source']:
  backup=b/'NCD_prebatch_source'/hashlib.sha256(p.read_bytes()).hexdigest()/p.name;backup.parent.mkdir(parents=True,exist_ok=True);backup.write_bytes(p.read_bytes())
 p.write_text(row['source'])
(b/'NCD_focus_plan.json').write_text(json.dumps(x['plan'],indent=2)+'\\n');(b/'NCD_focus_host.py').write_text(x['runner'])
'''
 for retry in range(11):
  r=rpc(code)
  if r.returncode==0:break
  if r.returncode==78 and retry<10:time.sleep(180);continue
  raise SystemExit('STOP batch setup '+r.stdout+r.stderr)
 launch=f'''from pathlib import Path
import subprocess,json,time
b=Path({B!r});m=b/'NCD_focus_submitted.json';assert not m.exists(),'never submit twice'
with (b/'NCD_focus.log').open('wb') as f:p=subprocess.Popen(['python3','NCD_focus_host.py'],cwd=b,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
m.write_text(json.dumps(dict(pid=p.pid,utc=time.time())));print(m.read_text())
'''
 (E/'NCD_BATCH_ACTIVE').write_text(hashlib.sha256((E/'NCD_focus_plan.json').read_bytes()).hexdigest()+'\n')
 r=rpc(launch,submitted=True);print(r.returncode,r.stdout,r.stderr)
elif mode=='recover':
 code=f'''from pathlib import Path
import json
b=Path({B!r});names=['NCD_focus_state.json','NCD_focus.log','NCD_focus_submitted.json','NCD_focus_initial_reservation.json','NCD_focus_initial_barrier.log']
s=b/'NCD_focus_state.json'
if s.exists():
 for row in json.loads(s.read_text())['report']:
  a=row['attempt'];names += [a+'.json',a+'-reservation.json',a+'-launcher.log',a+'/receipt.json',a+'/stdout.log',a+'/time.log']
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file()}}))
'''
 r=rpc(code);assert r.returncode==0,r.stderr
 out=json.loads(r.stdout)
 for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 state=json.loads(out.get('NCD_focus_state.json','{}'));print(json.dumps(dict(status=state.get('status'),latest=state.get('report',[])[-3:])))
 if state.get('status')=='terminal':(E/'NCD_BATCH_ACTIVE').unlink(missing_ok=True)
 # Authoritative per-attempt receipts are appended once only.
 known={json.loads(l)['attempt'] for l in (E/'NCD_ATTEMPTS.jsonl').read_text().splitlines()}
 with (E/'NCD_ATTEMPTS.jsonl').open('a') as f:
  for n,s in out.items():
   if n.endswith('/receipt.json') and json.loads(s)['attempt'] not in known:f.write(json.dumps(json.loads(s))+'\n')
else:raise SystemExit('unknown mode')
