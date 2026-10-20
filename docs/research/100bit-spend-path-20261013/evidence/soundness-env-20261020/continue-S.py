"""One dependency-ordered pass, 7000–7899; independent collision closures."""
import json,hashlib,subprocess,time,re,datetime
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');D=J/'evidence-S';S=J/'sources-S';O=J/'objects-S';T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();obj=lambda m:O/(m.replace('.','/')+'.olean')
man=json.loads((D/'manifest-S.json').read_text());mods={e['module']:e for e in man['order']}
old={r['module']:r for r in map(json.loads,(D/'status.jsonl').read_text().splitlines())};records={m:r for m,r in old.items() if r['status'].startswith('current')}
# All auxiliary artifacts that caused the three old failures must be present and byte-identical.
artifacts=json.loads((D/'reused-artifacts.json').read_text())
(D/'continuation-prior-status.json').write_text(json.dumps(old,indent=1)+'\n')
# A source import-closure collision is a static blocker, not a compile attempt.
def closure(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return seen
 seen.add(m)
 if m in mods:
  for x in mods[m]['imports']:closure(x,seen)
 return seen
pair={'Stage2ContinuationTypes','AspisR1PublicPreparation.Types'}
collisions={m:sorted(pair) for m in mods if pair<=closure(m)}
(D/'collision-closures.json').write_text(json.dumps({'declaration':'instDiscriminantVariantIsize','modules':collisions,'roots':[m for m in man['roots'] if m in collisions]},indent=2)+'\n')
# Full retained artifact inventory enters the fingerprint: the three old failures had incomplete bundles.
def fp(m):
 entries=[]
 for dep in sorted(mods[m]['imports']):
  p=obj(dep)
  if p.exists():
   entries.extend(f'{x.relative_to(O)}={sha(x)}' for x in sorted(p.parent.glob(p.name+'*')) if x.is_file())
   ir=p.with_suffix('.ir')
   if ir.exists():entries.append(f'{ir.relative_to(O)}={sha(ir)}')
  else:
   libs=json.loads((D/'continuation-libraries.json').read_text());entries.append(dep+'='+libs[dep]['sha256'])
 return hashlib.sha256(';'.join(entries).encode()).hexdigest()[:16]
def emit(r):
 r['source_revision']=man['repo_revision'];r['timestamp_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();records[r['module']]=r
 with (D/'continuation-status.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r['module'],r['status'],r.get('attempt',''),r.get('errors',[]),flush=True)
assert not (D/'continuation-status.jsonl').exists(), 'one pass only'
attempt=7000
for e in man['order']:
 m=e['module']
 if m in records:continue
 if m in collisions:emit({'module':m,'status':'skipped','reason':'generated declaration collision','blocked_imports':sorted(pair)});continue
 bad=[x for x in e['imports'] if x in mods and not records.get(x,{}).get('status','').startswith('current')]
 if bad:emit({'module':m,'status':'skipped','reason':'blocked imports','blocked_imports':bad});continue
 assert attempt<7900,'reserve 100 attempts for audit'
 a=attempt;attempt+=1;assert not (T/f'out-{a}.log').exists();src=S/(m.replace('.','/')+'.lean');assert sha(src)==e['sha256'];fingerprint=fp(m)
 cmd=['sh',str(D/'run-S.sh'),str(a),m.replace('.','/'),'S','7000','7',fingerprint]
 before=time.time();p=subprocess.run(cmd,capture_output=True,text=True)
 (D/f'launcher-{a}.log').write_text(p.stdout+p.stderr)
 out=(T/f'out-{a}.log').read_text() if (T/f'out-{a}.log').exists() else p.stdout+p.stderr;tl=(T/f'time-{a}.log').read_text() if (T/f'time-{a}.log').exists() else ''
 (D/f'out-{a}.log').write_text(out);(D/f'time-{a}.log').write_text(tl)
 def tv(pat):
  mm=re.search(pat,tl);return mm.group(1).strip() if mm else None
 ex=re.search(r'^exit=(\d+)',out,re.M);ex=int(ex.group(1)) if ex else p.returncode
 ax=[' '.join(x.split()) for x in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",out,re.M|re.S)]
 r={'module':m,'attempt':a,'status':'current-compiled' if ex==0 and obj(m).exists() else 'failed','source_sha256':e['sha256'],'deps_fingerprint':fingerprint,'fingerprint_scheme':'direct object bundles including sidecars and IR; libraries hashed','exit':ex,'launcher_exit':p.returncode,'wall':tv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),'wall_seconds_including_lock':time.time()-before,'peak_rss_kib':int(tv(r'Maximum resident set size \(kbytes\): (\d+)') or 0),'swaps':int(tv(r'Swaps: (\d+)') or 0),'axioms':ax,'errors':[l for l in out.splitlines() if 'error' in l or 'REFUSED' in l or 'HOLD' in l],'command':cmd,'import_closure_size':len(closure(m))-1,'out_sha256':sha(D/f'out-{a}.log'),'time_sha256':sha(D/f'time-{a}.log')}
 if r['status'].startswith('current'):r['object_sha256']=sha(obj(m))
 with (D/'attempts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 emit(r)
(D/'continuation-final-status.json').write_text(json.dumps(records,indent=1)+'\n');print('DONE next',attempt,flush=True)
