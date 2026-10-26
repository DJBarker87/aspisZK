"""Sequential env-J object recovery. No writes outside authorized recovery roots."""
from pathlib import Path
import subprocess,json,hashlib,re,time,datetime,os,sys
B=Path('/home/dombarker/project-offloads'); T=B/'aspis-fs-generic-20261006/evidence';H=B/'r1-privacy-build-integration-20261019';J=B/'aspis-joint-20261019';U=B/'codex-cx-import-union-20261022'
rows=json.loads((T/'EJR_restored-sources.json').read_text());env=json.loads((H/'env/J.json').read_text());paths=[Path(p) for p in env['LEAN_PATH'].split(':')]; roots={'joint':J,'union':U}
REV=(T/'EJR_revision.txt').read_text().strip();budget=799

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def imports(p):
 s=p.read_text();s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
 return [m.replace('.','/') for ln in s.splitlines() if re.match(r'^\s*(?:public\s+|private\s+)?import\s',ln) for m in re.sub(r'^\s*(?:public\s+|private\s+)?import\s+','',ln).split() if re.fullmatch(r'[\w.]+',m)]
def dep_paths(r):
 ps=[roots[r['workspace']]/'objects']+paths
 return ps
def deps(r):
 out=[]
 for m in r['imports']:
  p=next((p/(m+'.olean') for p in dep_paths(r) if (p/(m+'.olean')).is_file()),None)
  out.append(dict(module=m,path=str(p) if p else None,sha256=sha(p) if p else None))
 return out
for r in rows:
 r['imports']=imports(Path(r['host_path']));r['key']=r['workspace']+':'+r['module']
results=T/'EJR_attempts.jsonl';past=[json.loads(l) for l in results.read_text().splitlines()] if results.exists() else []
attempted={r['key'] for r in past};succeeded={r['key'] for r in past if r['exit']==0};attempt=30000+len(past)

def admit(label):
 for retry in range(11):
  p=T/(label+f'-reservation-{retry}.json');log=T/(label+f'-reservation-{retry}.log')
  with log.open('w') as f:rc=subprocess.run(['python3',str(B/'codex-cx-s2x-20261023/S2X_reservation.py'),str(p)],stdout=f,stderr=subprocess.STDOUT).returncode
  if not p.exists():
   if retry==0:time.sleep(30);continue
   raise RuntimeError('reservation JSON absent: '+str(log))
  d=json.loads(p.read_text())
  if d.get('allowed'):return {'receipt':str(p),'retries':retry}
  if rc not in (0,78):raise RuntimeError('reservation failure '+str(log))
  if retry==10:raise RuntimeError('reservation refused ten retries')
  print('reservation wait',label,retry,flush=True);time.sleep(180)

def save_state(pending,reason):
 (T/'EJR_progress.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),attempts=len(past),successes=len(succeeded),budget=800,next_attempt=attempt,reason=reason,pending=[dict(key=r['key'],missing=[d['module'] for d in deps(r) if not d['path']]) for r in pending]),indent=2)+'\n')
pending=[r for r in rows if r['key'] not in attempted]
while pending and len(past)<budget:
 ready=[]
 for r in pending:
  ds=deps(r)
  if all(d['path'] for d in ds):ready.append((r,ds))
 if not ready:save_state(pending,'no dependency-ready module; missing objects require recovery');break
 # Prioritize the R1Z base to recover privacy functionality promptly.
 ready.sort(key=lambda rd:(not rd[0]['module'].startswith('R1Z/'),rd[0]['workspace']!='joint',rd[0]['module']))
 r,ds=ready[0];label='EJR-'+str(attempt);admission=admit(label);root=roots[r['workspace']];src=Path(r['host_path']);assert sha(src)==r['source_sha256'];obj=root/'objects'/(r['module']+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 fp=hashlib.sha256(json.dumps(ds,sort_keys=True).encode()).hexdigest();start=time.monotonic()
 if r['workspace']=='joint':
  cmd=['sh',str(H/'tools/run-joint.sh'),str(attempt),r['module'],'J','7000','8',fp]
  with (T/(label+'-launcher.log')).open('w') as f:outer=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
  out=T/f'out-{attempt}.log';tim=T/f'time-{attempt}.log'
  if not tim.exists():raise RuntimeError('launcher did not execute: '+str(T/(label+'-launcher.log')))
 else:
  out=T/f'out-{attempt}.log';tim=T/f'time-{attempt}.log'
  cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(tim),'timeout','900','python3',str(T/'run2.py'),str(H/'env/J.json'),str(root/'objects'),str(root/'sources'),str(obj),str(src),'7000']
  with out.open('w') as f:outer=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
 s=out.read_text();ts=tim.read_text();em=re.search(r'Exit status:\s*(\d+)',ts);ec=int(em[1]) if em else outer
 axioms=[l for l in s.splitlines() if 'axioms' in l]
 if any('sorryAx' in l for l in axioms):ec=90
 record=dict(key=r['key'],attempt=attempt,module=r['module'],workspace=r['workspace'],source_sha256=r['source_sha256'],source_revision=REV,source_blob_revision=r['revision'],command=cmd,driver_command=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',str(root/'sources'),'-o',str(obj),str(src)],deps=ds,deps_fingerprint=fp,exit=ec,outer_exit=outer,wall_seconds=time.monotonic()-start,time_log=ts,peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',ts)[1]) if 'Maximum resident' in ts else None,swaps=int(re.search(r'Swaps:\s*(\d+)',ts)[1]) if 'Swaps:' in ts else None,axioms=axioms,errors=[l for l in s.splitlines() if 'error:' in l],admission=admission,caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),object_sha256=sha(obj) if obj.exists() and ec==0 else None,object_bytes=obj.stat().st_size if obj.exists() and ec==0 else None)
 with results.open('a') as f:f.write(json.dumps(record)+'\n')
 past.append(record);attempted.add(r['key']);pending.remove(r)
 if ec==0:succeeded.add(r['key'])
 # Failed outputs must not become dependency providers. Preserve diagnostics, not a bad olean.
 elif obj.exists():obj.rename(obj.with_suffix('.EJR-failed-olean'))
 print(label,r['key'],'exit',ec,'successes',len(succeeded),'wall',record['wall_seconds'],flush=True)
 attempt+=1;save_state(pending,'building')
 if ec in (124,137) or 'excessive memory' in s.lower() or 'out of memory' in s.lower():
  print('resource failure isolated; source will not be retried',r['key'],flush=True)
else:save_state(pending,'budget reached' if len(past)>=budget else 'all selected sources attempted')
print('STOP',len(past),'attempts',len(succeeded),'successes',flush=True)
