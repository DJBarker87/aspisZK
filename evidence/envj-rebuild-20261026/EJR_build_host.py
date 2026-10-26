"""Sequential env-J object recovery. No writes outside authorized recovery roots."""
from pathlib import Path
import subprocess,json,hashlib,re,time,datetime,os,sys,shutil
B=Path('/home/dombarker/project-offloads'); T=B/'aspis-fs-generic-20261006/evidence';H=B/'r1-privacy-build-integration-20261019';J=B/'aspis-joint-20261019';U=B/'codex-cx-import-union-20261022'
rows=json.loads((T/'EJR_all-restored-sources.json').read_text());env=json.loads((H/'env/J.json').read_text());paths=[Path(p) for p in env['LEAN_PATH'].split(':')]; roots={'joint':J,'union':U}
REV=(T/'EJR_revision.txt').read_text().strip();budget=int(os.environ.get('EJR_CUMULATIVE_BUILD_LIMIT','799'))

_hash_cache={}
def sha(p):
 st=p.stat();key=(str(p),st.st_size,st.st_mtime_ns)
 if key not in _hash_cache:_hash_cache[key]=hashlib.sha256(p.read_bytes()).hexdigest()
 return _hash_cache[key]
def imports(p):
 s=p.read_text();s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
 return [m.replace('.','/') for ln in s.splitlines() if re.match(r'^\s*(?:public\s+|private\s+)?import\s',ln) for m in re.sub(r'^\s*(?:public\s+|private\s+)?import\s+','',ln).split() if re.fullmatch(r'[\w.]+',m)]
def dep_paths(r):
 ps=[roots[r['workspace']]/'objects']+paths
 return ps
def deps(r):
 out=[]
 for m in r['imports']:
  own=r['workspace']+':'+m
  blocked=own in selected_keys and own not in succeeded
  p=None
  if not blocked:
   if '/' in m:
    first=next((p for p in dep_paths(r) if (p/m.split('/')[0]).is_dir()),None)
    if first is not None and (first/(m+'.olean')).is_file():p=first/(m+'.olean')
   else:p=next((p/(m+'.olean') for p in dep_paths(r) if (p/(m+'.olean')).is_file()),None)
  out.append(dict(module=m,path=str(p) if p else None,sha256=sha(p) if p else None))
 return out

def mirror_namespaces():
 # Lean selects a namespace directory as a unit. Provide complete fallback
 # views using symlinks, preserving concrete files compiled in each workspace.
 for ws,root in roots.items():
  target=root/'objects'
  for prefix in sorted(({'Aeneas','AeneasMeta'} | {r['module'].split('/')[0] for r in rows if r['workspace']==ws and '/' in r['module']})):
   if (target/prefix).is_symlink():continue
   seen=set()
   for base in paths:
    if base==target:continue
    d=base/prefix
    if not d.is_dir():continue
    for src in sorted(d.rglob('*')):
     if not src.is_file() or not any(str(src).endswith(e) for e in ['.olean','.olean.private','.olean.server','.ir']):continue
     rel=src.relative_to(base)
     if rel in seen:continue
     try:canonical=src.resolve(strict=True)
     except (RuntimeError,OSError):continue
     dest=target/rel
     if canonical==dest:continue
     seen.add(rel)
     if dest.exists() and not dest.is_symlink():continue
     if dest.is_symlink():
      if dest.resolve()==canonical:continue
      dest.unlink()
     dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(canonical)
  # A dangling earlier .olean symlink also shadows a later valid file.
  # Alias direct unqualified imports in the owned output root, not in caches.
  bound={r['namespace'] for r in json.loads((T/'EJR-namespace-bindings.json').read_text())} if (T/'EJR-namespace-bindings.json').exists() else set()
  flat={m for rr in rows if rr['workspace']==ws for m in rr['imports'] if '/' not in m and m not in bound}
  for m in sorted(flat):
   dest=target/(m+'.olean')
   if dest.exists() and not dest.is_symlink():continue
   canonical=None
   for base in paths:
    candidate=base/(m+'.olean')
    if base==target or not candidate.is_file():continue
    candidate=candidate.resolve()
    if candidate!=dest:canonical=candidate;break
   if canonical is None:continue
   if dest.is_symlink():
    if dest.resolve()==canonical:continue
    dest.unlink()
   dest.symlink_to(canonical)

for r in rows:
 r['imports']=imports(Path(r['host_path']));r['key']=r['workspace']+':'+r['module']
results=T/'EJR_attempts.jsonl';past=[json.loads(l) for l in results.read_text().splitlines()] if results.exists() else []
attempted={r['key'] for r in past};succeeded={r['key'] for r in past if r['exit']==0};attempt=30000+len(past)
selected_keys={r['key'] for r in rows}
reuses_file=T/'EJR_reuses.jsonl'
reuses=[json.loads(l) for l in reuses_file.read_text().splitlines()] if reuses_file.exists() else []
succeeded.update(r['key'] for r in reuses);attempted.update(r['key'] for r in reuses)
latest_by_key={r['key']:r for r in past}
repair_keys={r['key'] for r in latest_by_key.values() if r['exit']!=0 and any('error: object file' in e and 'does not exist' in e for e in r['errors'])} - {r['key'] for r in reuses}

def try_reuse(r,ds):
 fingerprint=lambda dd:[(d['module'].replace('.','/'),d['sha256']) for d in dd]
 for old in past:
  if old['exit'] or old['workspace'] not in roots or old['module']!=r['module'] or old['source_sha256']!=r['source_sha256'] or fingerprint(old['deps'])!=fingerprint(ds):continue
  source=roots[old['workspace']]/'objects'/(r['module']+'.olean')
  if not source.is_file() or sha(source)!=old['object_sha256']:continue
  dest=roots[r['workspace']]/'objects'/(r['module']+'.olean')
  source=source.resolve()
  if dest.exists() and not dest.is_symlink() and sha(dest)!=old['object_sha256']:raise RuntimeError('unexpected existing output '+str(dest))
  if dest.is_symlink():dest.unlink()
  dest.parent.mkdir(parents=True,exist_ok=True)
  if not dest.exists():dest.symlink_to(source)
  companions=[]
  for ext in ['.olean.private','.olean.server','.ir']:
   cp=source.with_suffix(ext) if ext=='.ir' else Path(str(source)+ext.removeprefix('.olean'))
   dp=dest.with_suffix(ext) if ext=='.ir' else Path(str(dest)+ext.removeprefix('.olean'))
   if cp.is_file():
    if dp.is_symlink():dp.unlink()
    if not dp.exists():dp.symlink_to(cp.resolve())
    companions.append(dict(path=str(dp),sha256=sha(dp)))
  record=dict(key=r['key'],module=r['module'],workspace=r['workspace'],source_sha256=r['source_sha256'],deps=ds,compiled_attempt=old['attempt'],object_sha256=sha(dest),object_bytes=dest.stat().st_size,source=str(source),target=str(dest),companions=companions,reason='same module/source and selected dependency object hashes; no compile rerun')
  with reuses_file.open('a') as f:f.write(json.dumps(record)+'\n')
  reuses.append(record);succeeded.add(r['key']);attempted.add(r['key']);print('REUSED',r['key'],'from',old['attempt'],flush=True);return True
 return False

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
pending=[r for r in rows if r['key'] not in attempted or r['key'] in repair_keys]
while pending and len(past)<budget:
 mirror_namespaces()
 ready=[]
 for r in pending:
  ds=deps(r)
  if all(d['path'] for d in ds):ready.append((r,ds))
 if not ready:save_state(pending,'no dependency-ready module; missing objects require recovery');break
 # Prioritize the R1Z base to recover privacy functionality promptly.
 ready.sort(key=lambda rd:(not rd[0]['module'].startswith('R1Z/'),rd[0]['workspace']!='joint',rd[0]['module']))
 r,ds=ready[0]
 if try_reuse(r,ds):
  pending.remove(r);save_state(pending,'building; identical objects reused');continue
 label='EJR-'+str(attempt);admission=admit(label);root=roots[r['workspace']];src=Path(r['host_path']);assert sha(src)==r['source_sha256'];obj=root/'objects'/(r['module']+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 if obj.is_symlink():obj.unlink()
 elif obj.exists():raise RuntimeError('refuse overwriting existing regular object '+str(obj))
 context={n:sha(T/n) for n in ['EJR-namespace-bindings.json','EJR-library-published.json','EJR-library-ir-restored.json']}
 fp=hashlib.sha256(json.dumps(dict(direct_dependencies=ds,physical_library_context=context),sort_keys=True).encode()).hexdigest();start=time.monotonic()
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
 lean_exit=ec
 if any('sorryAx' in l for l in axioms):ec=90
 record=dict(key=r['key'],attempt=attempt,module=r['module'],workspace=r['workspace'],source_sha256=r['source_sha256'],source_revision=REV,source_blob_revision=r['revision'],command=cmd,driver_command=[env['LEAN'],'-j1','-M7000','-DElab.async=false','-R',str(root/'sources'),'-o',str(obj),str(src)],deps=ds,deps_fingerprint=fp,exit=ec,lean_exit=lean_exit,validation_exit=ec,outer_exit=outer,wall_seconds=time.monotonic()-start,time_log=ts,peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',ts)[1]) if 'Maximum resident' in ts else None,swaps=int(re.search(r'Swaps:\s*(\d+)',ts)[1]) if 'Swaps:' in ts else None,axioms=axioms,errors=[l for l in s.splitlines() if 'error:' in l],admission=admission,caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),object_sha256=sha(obj) if obj.exists() and ec==0 else None,object_bytes=obj.stat().st_size if obj.exists() and ec==0 else None,namespace_loader_repair=r['key'] in repair_keys,physical_library_context=context)
 with results.open('a') as f:f.write(json.dumps(record)+'\n')
 past.append(record);attempted.add(r['key']);pending.remove(r)
 if ec==0:succeeded.add(r['key'])
 # Failed outputs must not become dependency providers. Preserve diagnostics, not a bad olean.
 elif obj.exists():obj.rename(obj.with_suffix('.EJR-failed-olean'))
 print(label,r['key'],'exit',ec,'successes',len(succeeded),'wall',record['wall_seconds'],flush=True)
 attempt+=1;save_state(pending,'building')
 if any('error: object file' in e and 'does not exist' in e for e in record['errors']):raise RuntimeError('namespace preflight mismatch; stop coordinator after recorded attempt '+str(attempt-1))
 if ec in (124,137) or 'excessive memory' in s.lower() or 'out of memory' in s.lower():
  print('resource failure isolated; source will not be retried',r['key'],flush=True)
else:save_state(pending,'budget reached' if len(past)>=budget else 'all selected sources attempted')
print('STOP',len(past),'attempts',len(succeeded),'successes',flush=True)
