"""Host-only final hash/fingerprint verification; no compiler invocation."""
import json,hashlib,collections,tarfile
from pathlib import Path
D=Path(__file__).resolve().parent;J=D.parent;O=J/'objects-S';S=J/'sources-S'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
man=json.loads((D/'manifest-S.json').read_text());mods={e['module']:e for e in man['order']};rows=json.loads((D/'continuation-final-status.json').read_text());current={m:r for m,r in rows.items() if r['status'].startswith('current')};libs=json.loads((D/'continuation-libraries.json').read_text());problems=[]
objects={m:sha(O/(m.replace('.','/')+'.olean')) for m in current}
def bundle_fp(e):
 entries=[]
 for dep in sorted(e['imports']):
  p=O/(dep.replace('.','/')+'.olean')
  if p.exists():
   entries.extend(f'{x.relative_to(O)}={sha(x)}' for x in sorted(p.parent.glob(p.name+'*')) if x.is_file())
   ir=p.with_suffix('.ir')
   if ir.exists():entries.append(f'{ir.relative_to(O)}={sha(ir)}')
  else:entries.append(dep+'='+libs[dep]['sha256'])
 return hashlib.sha256(';'.join(entries).encode()).hexdigest()[:16]
for m,r in current.items():
 e=mods[m]
 if sha(S/(m.replace('.','/')+'.lean'))!=e['sha256'] or r['source_sha256']!=e['sha256']:problems.append(['source',m])
 if objects[m]!=r['object_sha256']:problems.append(['object',m])
 deps=sorted(x for x in e['imports'] if x in mods)
 if any(x not in current for x in deps):problems.append(['noncurrent-import',m]);continue
 fp=bundle_fp(e) if r.get('fingerprint_scheme') else hashlib.sha256(';'.join(f'{x}={objects[x]}' for x in deps).encode()).hexdigest()[:16]
 if fp!=r['deps_fingerprint']:problems.append(['fingerprint',m])
for m,r in libs.items():
 if sha(Path(r['path']))!=r['sha256']:problems.append(['library',m])
ats=list(map(json.loads,(D/'attempts.jsonl').read_text().splitlines()));new=[r for r in ats if 7000<=r['attempt']<7900]
if len({r['module'] for r in new})!=len(new):problems.append(['repeated-continuation-module'])
if len({r['attempt'] for r in ats})!=len(ats):problems.append(['repeated-attempt-number'])
repeats={m:[r['attempt'] for r in ats if r['module']==m] for m,n in collections.Counter(r['module'] for r in ats).items() if n>1}
assert set(repeats)<={'AspisR1BatchedActualCounter','AspisR1BatchedReducerBridge','BatchedWeightsActualReducer','R1LiteralTranscript'}
# Verify every retained auxiliary artifact, including the earlier missing server/IR data.
arts=json.loads((D/'reused-artifacts.json').read_text())
for r in arts:
 p=Path(r['path'].replace('/objects/','/objects-S/'))
 if sha(p)!=r['sha256']:problems.append(['retained-artifact',str(p)])
cache=Path('/home/dombarker/project-offloads/root-comppoly432-retained-cache-20261019');inventory=[{'path':str(p),'sha256':sha(p),'size':p.stat().st_size} for p in sorted(cache.rglob('*')) if p.is_file()]
(D/'retained-comppoly-inventory.json').write_text(json.dumps({'source_repository':'https://github.com/Verified-zkEVM/CompPoly','source_revision':'4165a87dd9a9ede48ee4dc5b4fe825604b8bb932','release_tag':'4.32.0-cache','evidence_packet':'extractor-gcd-remainder-polynomial-bound-20261019/ActualScaledDivisorMonic/command.json','files':inventory},indent=1)+'\n')
rep={'current_modules_checked':len(current),'library_identities_checked':len(libs),'retained_artifacts_checked':len(arts),'continuation_attempts':len(new),'modules_attempted_once_in_continuation':len({r['module'] for r in new}),'authorized_new_input_attempts_after_old_failures':repeats,'problems':problems,'compiler_started':False,'note':'Source/object/dependency bundles and libraries verified. Two disjoint generated-instance import closures; no joint-union compatibility claim.'}
(D/'coherence-final.json').write_text(json.dumps(rep,indent=2)+'\n');print(json.dumps(rep,indent=2));assert not problems
(D/'current-objects.json').write_text(json.dumps([{'module':m,'source_sha256':mods[m]['sha256'],'object_sha256':objects[m],'status':r['status']} for m,r in sorted(current.items())],indent=2)+'\n')

# Final source archive is retained on the host; only hashes/sizes are delivered.
p=D/'sources-env2.tar'
with tarfile.open(p,'w') as tf:
 for e in man['order']:tf.add(S/(e['module'].replace('.','/')+'.lean'),arcname=e['module'].replace('.','/')+'.lean')
(D/'source-archive-env2.json').write_text(json.dumps({'path':str(p),'sha256':sha(p),'size':p.stat().st_size,'modules':len(mods),'contents':'exact manifest source closure; no compiled objects; retained on host'},indent=2)+'\n')
# Library paths are resolved read-only identities, not source-owner substitutions.
man['libraries']={m:r['path'] for m,r in libs.items()}
(D/'manifest-S.json').write_text(json.dumps(man,indent=1)+'\n')
