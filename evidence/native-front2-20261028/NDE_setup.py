from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-native-front2-20261028'
# Restore all project source from immutable release objects, never another lane's patches.
names=subprocess.check_output(['git','ls-tree','-r','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387']).decode().splitlines()
owned={n:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n]).decode() for n in names if (n.startswith(('crates/','programs/')) and n.endswith('.rs')) or n=='Cargo.lock'}
code='''from pathlib import Path
import json,hashlib,shutil
x=json.loads(PAYLOAD);b=Path(x['B']);ad=json.loads((b/'NDE_SETUP-reservation.json').read_text());assert ad['allowed'] is True
old=b.parent/'codex-cx-native-cpilot-20261028/NCO_src';s=b/'NDE_src';assert not s.exists();s.mkdir()
for p in old.rglob('*'):
 if not p.is_file():continue
 n=str(p.relative_to(old))
 if any(v.startswith(('NCO_','NCH_')) for v in Path(n).parts):continue
 q=s/n;q.parent.mkdir(parents=True,exist_ok=True)
 if n in x['owned']:q.write_text(x['owned'][n])
 elif p.name=='Cargo.toml':q.write_bytes(p.read_bytes())
 else:q.symlink_to(p.resolve())
for n,v in x['owned'].items():
 q=s/n
 if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.write_text(v)
c=b.parent/'codex-cx-front2-cache-20261028';c.mkdir(exist_ok=True);imports={}
for base in ['codex-cx-cpilot-cache-20261028','codex-cx-leaf-cache-20261027']:
 for p in (b.parent/base).rglob('*'):
  if not p.is_file():continue
  n=p.relative_to(b.parent/base);q=c/n;h=hashlib.sha256(p.read_bytes()).hexdigest()
  if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
  imports[str(p)]=dict(sha256=h,selected_sha256=hashlib.sha256(q.read_bytes()).hexdigest())
coherent=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:(b/n).write_bytes((coherent/n).read_bytes())
lib=[coherent/'objects/Aeneas.olean']+list((coherent/'objects/Aeneas').rglob('*.olean'))
for n in ['NDE_tmp','NDE_generated','NDE_objects']:(b/n).mkdir(exist_ok=True)
pins={str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}
(b/'NDE_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(dict(admission=ad,source_sha256=pins,cache_imports=imports,library={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in lib})))
'''.replace('PAYLOAD',repr(json.dumps(dict(B=B,owned=owned))))
r=subprocess.run(['ssh','-o','ConnectTimeout=20','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NDE_SETUP.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
(E/'NDE_SOURCE.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('setup complete')
