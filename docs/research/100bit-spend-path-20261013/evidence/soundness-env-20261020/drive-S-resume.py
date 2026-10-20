"""One pass through the source closure; no retries. All compiler work on the host."""
import json,hashlib,os,re,shutil,subprocess,time,datetime
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
H=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019')
D=J/'evidence-S'; O=J/'objects-S'; S=J/'sources-S'
man=json.loads((D/'manifest-S.json').read_text()); mods={e['module']:e for e in man['order']}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
path=lambda root,m:root/(m.replace('.','/')+'.olean')
records={}; start=time.time()
def emit(r):
 r['source_revision']=man['repo_revision'];r['timestamp_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with (D/'status.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 records[r['module']]=r
 print(r['module'],r['status'],r.get('attempt',''),r.get('reason',''),flush=True)
records={r['module']:r for r in map(json.loads,(D/'status.jsonl').read_text().splitlines())}
(D/'driver.pid').write_text(str(os.getpid())+'\n')
# Snapshot J provenance; the only search path for non-library objects in S is objects-S.
old={}
for line in (J/'evidence/attempts.jsonl').read_text().splitlines():
 r=json.loads(line)
 if r.get('exit')==0:old[r['module']]=r
libs={}
env=json.loads((H/'env/J.json').read_text())
for m in man['libraries']:
 hits=[Path(d)/(m.replace('.','/')+'.olean') for d in env['LEAN_PATH'].split(':')]
 p=next((p for p in hits if p.exists()),None)
 libs[m]={'path':str(p) if p else None,'sha256':sha(p) if p else None,'size':p.stat().st_size if p else None}
(D/'libraries.json').write_text(json.dumps(libs,indent=2)+'\n')
missing={p[1] for p in man['problems'] if p[0]=='unresolved'}|{m for m,v in libs.items() if not v['path']}
# Reuse only recursively current J modules; preserve immutable copies and their full receipts.
reused={}
for m,e in []:  # J staging already completed; never restage or overwrite current S objects
 deps=[x for x in e['imports'] if x in mods]
 r=old.get(m); p=path(J/'objects',m); src=J/'sources'/(m.replace('.','/')+'.lean')
 if not r or not p.exists() or not src.exists() or sha(src)!=e['sha256'] or r.get('source_sha256')!=e['sha256']:continue
 if any(x not in reused for x in deps) or any(x in missing for x in e['imports']):continue
 fp=hashlib.sha256(';'.join(f'{x}={sha(path(J/"objects",x))}' for x in sorted(deps)).encode()).hexdigest()[:16]
 if r.get('deps_fingerprint'):
  if fp!=r['deps_fingerprint']:continue
 elif any(path(J/'objects',x).stat().st_mtime_ns>p.stat().st_mtime_ns for x in deps):continue
 # Existing module object must postdate its successful log, allowing timestamp rounding.
 log=T/f"out-{r['attempt']}.log"
 if not log.exists() or p.stat().st_mtime+5<log.stat().st_mtime:continue
 dst=path(O,m);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
 reused[m]=r
 emit({'module':m,'status':'current-reused','source_sha256':e['sha256'],'object_sha256':sha(dst),'deps_fingerprint':fp,'reused_receipt':r})
# Original reuse receipts remain immutable.
# Every unresolved module and its descendants are skipped; independent components proceed.
attempt=6450
order=[];seen=set()
def visit(m):
 if m in seen or m not in mods:return
 seen.add(m)
 for dep in mods[m]['imports']:visit(dep)
 order.append(m)
priority=['HchecksReaderComposition','DecoderInstanceBoundary','LiteralFreshAttemptBound','RawAdaptiveMembershipBound','AdaptiveMembershipSoundness','SpendRelation','SpendAppendBinding']
priority += [m for m in man['roots'] if m.startswith('Bin')]
priority += ['RawChecksAdaptiveFailureNoModel','RawExtractorCostComposedV2']
for m in priority+list(mods):visit(m)
for m in order:
 e=mods[m]
 if m in records:continue
 bad=[x for x in e['imports'] if x in missing or x in mods and not records.get(x,{}).get('status','').startswith('current')]
 if bad:
  emit({'module':m,'status':'skipped','reason':'blocked imports','blocked_imports':bad});continue
 while attempt<=6999 and (T/f'out-{attempt}.log').exists():attempt+=1
 if attempt>6999:
  emit({'module':m,'status':'skipped','reason':'assigned attempt range exhausted'});continue
 a=attempt;attempt+=1
 fp=hashlib.sha256(';'.join(f'{x}={sha(path(O,x))}' for x in sorted(e['imports']) if x in mods).encode()).hexdigest()[:16]
 src=S/(m.replace('.','/')+'.lean');assert sha(src)==e['sha256']
 cmd=['sh',str(D/'run-S.sh'),str(a),m.replace('.','/'),'S','7000','7',fp]
 before=time.time();p=subprocess.run(cmd,capture_output=True,text=True)
 (D/f'launcher-{a}.log').write_text(p.stdout+p.stderr)
 out=(T/f'out-{a}.log').read_text() if (T/f'out-{a}.log').exists() else p.stdout+p.stderr
 tl=(T/f'time-{a}.log').read_text() if (T/f'time-{a}.log').exists() else ''
 (D/f'out-{a}.log').write_text(out);(D/f'time-{a}.log').write_text(tl)
 def tv(pattern):
  mm=re.search(pattern,tl);return mm.group(1).strip() if mm else None
 ex=re.search(r'^exit=(\d+)',out,re.M);ex=int(ex.group(1)) if ex else p.returncode
 ax=[' '.join(x.split()) for x in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",out,re.M|re.S)]
 def closure(m,seen=None):
  seen=set() if seen is None else seen
  if m in seen:return seen
  seen.add(m)
  if m in mods:
   for x in mods[m]['imports']:closure(x,seen)
  return seen
 r={'module':m,'attempt':a,'status':'current-compiled' if ex==0 and path(O,m).exists() else 'failed','source_sha256':e['sha256'],'deps_fingerprint':fp,'exit':ex,'launcher_exit':p.returncode,'wall':tv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),'wall_seconds_including_lock':time.time()-before,'peak_rss_kib':int(tv(r'Maximum resident set size \(kbytes\): (\d+)') or 0),'swaps':int(tv(r'Swaps: (\d+)') or 0),'axioms':ax,'errors':[l for l in out.splitlines() if 'error' in l or 'REFUSED' in l or 'HOLD' in l],'command':cmd,'import_closure_size':len(closure(m))-1}
 if r['status'].startswith('current'):r['object_sha256']=sha(path(O,m))
 with (D/'attempts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 emit(r)
(D/'driver-wall.json').write_text(json.dumps({'wall_seconds':time.time()-start,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
print('DONE',flush=True)
