"""Recheck the recorded source/object graph and library identities; never compiles."""
import json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parent;J=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods={e['module']:e for e in json.loads((D/'manifest-S.json').read_text())['order']}
rows={r['module']:r for r in map(json.loads,(D/'status.jsonl').read_text().splitlines())}
current={m:r for m,r in rows.items() if r['status'].startswith('current')}
objects={m:sha(J/'objects-S'/(m.replace('.','/')+'.olean')) for m in current}
problems=[]
for m,r in current.items():
 e=mods[m];p=J/'sources-S'/(m.replace('.','/')+'.lean')
 if sha(p)!=e['sha256'] or r['source_sha256']!=e['sha256']:problems.append(['source',m])
 if objects[m]!=r['object_sha256']:problems.append(['object',m])
 deps=sorted(x for x in e['imports'] if x in mods)
 if any(x not in current for x in deps):problems.append(['noncurrent-import',m]);continue
 fp=hashlib.sha256(';'.join(f'{x}={objects[x]}' for x in deps).encode()).hexdigest()[:16]
 if fp!=r['deps_fingerprint']:problems.append(['fingerprint',m])
libs=json.loads((D/'libraries.json').read_text())
for m,r in libs.items():
 if not r['path'] or sha(Path(r['path']))!=r['sha256']:problems.append(['library',m])
attempts=list(map(json.loads,(D/'attempts.jsonl').read_text().splitlines()))
if len({r['module'] for r in attempts})!=len(attempts):problems.append(['repeated-source-module'])
if len({r['attempt'] for r in attempts})!=len(attempts):problems.append(['repeated-source-attempt'])
report={'current_modules_checked':len(current),'library_identities_checked':len(libs),'source_attempts':len(attempts),'source_modules_attempted_once':len({r['module'] for r in attempts}),'problems':problems,'compiler_started':False,'note':'All current source hashes, object hashes, dependency fingerprints and imported current states rechecked. External library identities match initial S preflight.'}
(D/'coherence-final.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));assert not problems
