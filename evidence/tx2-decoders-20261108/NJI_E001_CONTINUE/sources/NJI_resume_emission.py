"""Continue E001 after own opacity-name collector failed; NEVER rerun Charon."""
from pathlib import Path
import json,subprocess,hashlib,os
import NHR_stage as stage
E=Path(__file__).resolve().parent;out=E/'NJI_EMITTED'
p=json.loads((out/'NHR_PINS.json').read_text());llbc=out/'nji_tx2_decoders.llbc'
assert hashlib.sha256(llbc.read_bytes()).hexdigest()==p['llbc_sha256']
assert 'aeneas_exit' not in p
stage.validate(E/'NHR_workspace',E/'NJI_RESUME_PREFLIGHT','/home/dombarker/.cargo/bin/cargo')
for n,h in stage.PINS.items():assert stage.sha((stage.TOOLROOT/n).read_bytes())==h
d=json.loads((out/'NHR_DECLARATIONS.json').read_text());matched=[]
for i in range(8):
 row=next(x for x in d if x['id']==i);assert row['body_kind']==['Structured']
for b in p['opacity']:
 requested=b.get('selector',b['path']);actual=requested
 if requested=='aspis_statement::decode_digest_canonical':
  # The frozen lib.rs glob reexport resolves to this exact canonical owner.
  assert 'pub use atomic_statement::' in (E/'NHR_workspace/crates/aspis-statement/src/lib.rs').read_text()
  actual='aspis_statement::atomic_statement::decode_digest_canonical'
 hits=[r for r in d if [z['Ident'][0] if 'Ident' in z else '_' for z in r['name']]==actual.split('::')]
 assert hits and all(r['body_kind']=='Opaque' for r in hits)
 matched.append(dict(boundary=b,actual_owner=actual,matches=hits))
p['validated_opacity']=matched
r=subprocess.run(p['aeneas_command'],cwd=E,env=dict(os.environ,CARGO_NET_OFFLINE='true'))
p['aeneas_exit']=r.returncode;p['exit']=r.returncode;p['resume']='E001 same pinned LLBC; own collector canonical reexport repair; no Charon rerun'
p['outputs']={str(z.relative_to(out)):stage.sha(z.read_bytes()) for z in (out/'raw').rglob('*') if z.is_file()}
(out/'NJI_RESUMED_PINS.json').write_text(json.dumps(p,indent=2))
assert stage.sha((E/'NHR_workspace/Cargo.lock').read_bytes())==p['lock_before']
print(json.dumps(dict(aeneas_exit=r.returncode,outputs=len(p['outputs']))));raise SystemExit(r.returncode)
