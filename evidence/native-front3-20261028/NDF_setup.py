from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front3-20261028'
owned={n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n]).decode() for n in ['Cargo.lock','crates/aspis-core/src/r0_transcript.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs']}
owned['crates/aspis-r1-cost-probe/src/lib.rs']='#![cfg_attr(kani, feature(allocator_api))]\n'+owned['crates/aspis-r1-cost-probe/src/lib.rs']+'\n#[cfg(kani)]\nmod NDF_controls;\n'
x=dict(B=B,owned=owned)
code='''from pathlib import Path
import json,subprocess,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);b.mkdir(exist_ok=True)
with (b/'NDF_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NDF_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NDF_SETUP-reservation.json').read_text());assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
old=Path('/home/dombarker/project-offloads/codex-cx-native-cpilot-20261028/NCO_src');s=b/'NDF_src';assert not s.exists();s.mkdir()
for p in old.rglob('*'):
 if not p.is_file():continue
 n=str(p.relative_to(old))
 if any(v.startswith(('NCH_','NCO_')) for v in Path(n).parts):continue
 q=s/n;q.parent.mkdir(parents=True,exist_ok=True)
 if n in x['owned']:q.write_text(x['owned'][n])
 elif p.name=='Cargo.toml':q.write_bytes(p.read_bytes())
 else:q.symlink_to(p.resolve())
c=Path('/home/dombarker/project-offloads/codex-cx-front3-cache-20261028');c.mkdir(exist_ok=True);imports={}
for base in ['codex-cx-cpilot-cache-20261028','codex-cx-leaf-cache-20261027']:
 for p in (b.parent/base).rglob('*'):
  if not p.is_file():continue
  n=p.relative_to(b.parent/base);q=c/n;h=hashlib.sha256(p.read_bytes()).hexdigest()
  if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
  imports[str(p)]=dict(sha256=h,selected_sha256=hashlib.sha256(q.read_bytes()).hexdigest())
coherent=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:(b/n).write_bytes((coherent/n).read_bytes())
lib=[coherent/'objects/Aeneas.olean']+list((coherent/'objects/Aeneas').rglob('*.olean'))
(b/'NDF_tmp').mkdir();(b/'NDF_generated').mkdir();(b/'NDF_objects').mkdir()
pins={str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}
(b/'NDF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(dict(admission=a,admission_exit=r.returncode,source_sha256=pins,cache_imports=imports,library={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in lib})))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NDF_SETUP.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
(E/'NDF_SOURCE.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('setup complete')
