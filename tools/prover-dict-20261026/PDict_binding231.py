"""Read-only cached-object/source consistency check after the focused audit."""
from pathlib import Path
import hashlib,json
job=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026')
joint=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
h=job/'receipts231'
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
audit=json.loads((h/'23158-input.json').read_text())
expected={r['module']:r['object_sha256'] for r in audit['dependencies']}
objects=[]
for d in audit['dependencies']:
 p=Path(d['resolved_object']);v=sha(p);objects.append(dict(module=d['module'],expected=d['object_sha256'],actual=v,match=v==d['object_sha256'],size=p.stat().st_size))
latest={}
for p in sorted(h.glob('*-input.json')):
 x=json.loads(p.read_text());a=x['attempt'];out=Path(f'/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/out-{a}.log')
 if out.exists() and '\nexit=0\n' in out.read_text():latest[x['module']]=x
sources=[];dependency_mismatches=[]
for mod,x in sorted(latest.items()):
 p=joint/'sources'/(mod+'.lean');v=sha(p)
 sources.append(dict(module=mod,attempt=x['attempt'],source_sha256=x['source_sha256'],current_sha256=v,match=v==x['source_sha256']))
 for d in x['dependencies']:
  if d['module'] in expected and expected[d['module']]!=d['object_sha256']:
   dependency_mismatches.append(dict(consumer=mod,dependency=d['module'],compiled_against=d['object_sha256'],audit_object=expected[d['module']]))
raw=[]
for n in ['ProverRwFullFuns','ProverRwFullTypes','ProverRwFullExternalTypes','ProverRwFullExternalFuns']:
 p=joint/'sources/R1Z'/(n+'.lean');raw.append(dict(module=n,sha256=sha(p),bytes=p.stat().st_size))
locks={}
for n in ['proof-quotient','proof-remaining']:
 p=job/'src/tools/prover-dict-20261026'/n/'Cargo.lock';locks[n]=dict(sha256=sha(p),text=p.read_text())
k=Path('/home/dombarker/.kani/kani-0.67.0')
toolchain=dict(kani='0.67.0',rustc=(k/'rustc-version').read_text(),toolchain=(k/'rust-toolchain-version').read_text(),binary_sha256={n:sha(k/'bin'/n) for n in ['kani-compiler','cbmc','kissat']})
y=dict(audit=23158,audit_source_sha256=audit['source_sha256'],deps_fingerprint=audit['deps_fingerprint'],dependency_objects=objects,own_sources=sources,all_current_objects_match=all(x['match'] for x in objects),all_current_sources_match=all(x['match'] for x in sources),compiled_dependency_mismatches=dependency_mismatches,raw_sources=raw,proof_crate_locks=locks,kani_toolchain=toolchain,qualification='Focused cached closure and input coherence only; no frozen release/ELF replay. All successful own modules compared against final audit object fingerprints.')
(job/'binding231-final.json').write_text(json.dumps(y,indent=2)+'\n')
print(json.dumps({k:v for k,v in y.items() if k in ['all_current_objects_match','all_current_sources_match','compiled_dependency_mismatches']}))
