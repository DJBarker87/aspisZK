"""Read-only full frozen Rust/source inventory of the reused scratch."""
from pathlib import Path
import subprocess,json,hashlib,shlex
E=Path(__file__).resolve().parent
R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
B='/home/dombarker/project-offloads/codex-cx-leaf-p6-9-20261027/LPi_src'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',R,'--','crates','programs']).decode().splitlines()+['Cargo.lock','Cargo.toml']
expected={f:hashlib.sha256(subprocess.check_output(['git','show',R+':'+f])).hexdigest() for f in files}
script='''import pathlib,hashlib,json
base=pathlib.Path(BASE)
files=FILES
out={}
for f in files:
 p=base/f
 if not p.is_file():out[f]={'missing':True};continue
 data=p.read_bytes();normalized=data
 marker={'crates/aspis-r1-cost-probe/src/lib.rs':b'\\n#[cfg(kani)] mod LPi_contracts;\\n', 'crates/aspis-r1-cost-probe/src/verifier.rs':b'\\n#[cfg(kani)] #[path="LPi_verifier.rs"] mod LPi_verifier;\\n'}.get(f)
 if marker:
  assert data.count(marker)==1,(f,'module count')
  normalized=data.split(marker)[0].rstrip(b'\\n')+b'\\n'
 out[f]={'bytes':len(data),'scratch_sha256':hashlib.sha256(data).hexdigest(),'normalized_sha256':hashlib.sha256(normalized).hexdigest(),'only_allowed_cfg_overlay':bool(marker)}
print(json.dumps(out))
'''.replace('BASE',repr(B)).replace('FILES',repr(files))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],capture_output=True,text=True,check=True)
actual=json.loads(r.stdout);errors=[]
for f,h in expected.items():
 actual[f]['frozen_sha256']=h
 if actual[f].get('normalized_sha256')!=h:errors.append(f)
result={'frozen_revision':R,'files':actual,'errors':errors,'repository_shipped_diff':subprocess.check_output(['git','diff','--name-only','HEAD','--','crates','programs']).decode().splitlines()}
(E/'LPi_SOURCE_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print('Frozen files',len(files),'mismatches',errors)
assert not errors and not result['repository_shipped_diff']
