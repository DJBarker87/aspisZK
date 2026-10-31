from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-leaves-20261029';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'crates','programs','Cargo.lock'],text=True).splitlines()
# Frozen values overwrite every potentially instrumented source in the imported scaffold.
owned={n:subprocess.check_output(['git','show',rev+':'+n]).decode() for n in paths if n.endswith(('.rs','.toml')) or n=='Cargo.lock'}
payload=json.dumps(dict(B=B,owned=owned,patch=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text()))
code='''from pathlib import Path
import json,subprocess,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);b.mkdir(exist_ok=True)
with (b/'NEC_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NEC_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NEC_SETUP-reservation.json').read_text());assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
old=b.parent/'codex-cx-native-cpilot-20261028/NCO_src';s=b/'NEC_src';assert not s.exists();s.mkdir()
for p in old.rglob('*'):
 if not p.is_file():continue
 n=str(p.relative_to(old))
 if any(v.startswith(('NCO_','NCH_')) for v in Path(n).parts):continue
 if n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:continue
 q=s/n;q.parent.mkdir(parents=True,exist_ok=True)
 if n in x['owned']:q.write_text(x['owned'][n])
 elif p.name=='Cargo.toml':q.write_bytes(p.read_bytes())
 else:q.symlink_to(p.resolve())
for n,v in x['owned'].items():
 if (s/n).exists():continue
 # Don't materialize independent crates excluded by the retained workspace.
 if n.startswith(('crates/','programs/')) and not (s/Path(n).parts[0]/Path(n).parts[1]).exists():continue
 q=s/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(v)
p=b/'NEC_KMX.patch';p.write_text(x['patch']);subprocess.run(['git','apply',str(p)],cwd=s,check=True)
pins={str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}
(b/'NEC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1))
print(json.dumps(dict(admission=a,admission_exit=r.returncode,source_sha256=pins)))
'''.replace('PAYLOAD',repr(payload))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NEC_NATIVE_SETUP.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout[-2000:]+r.stderr[-2000:]
(E/'NEC_NATIVE_SOURCE.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n')
print('native setup complete')
