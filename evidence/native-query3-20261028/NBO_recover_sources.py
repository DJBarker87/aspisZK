from NBO_host import *
import fcntl,hashlib,difflib
with (E/'NBO_SERIAL.lock').open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 r=py(f'''from pathlib import Path
import json
b=Path({B!r});out={{}}
for d in sorted(b.glob('NBO_[KG]*/sources/NBO_src')):
 p=d/'crates/aspis-r1-cost-probe/src/NBO_native.rs'
 if p.exists():out[d.parents[1].name]=p.read_text()
print(json.dumps(out))
''')
 assert r.returncode==0,r.stderr
 sources=json.loads(r.stdout)
 frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 name='crates/aspis-r1-cost-probe/src/candidate.rs'
 base=subprocess.check_output(['git','show',frozen+':'+name],text=True)
 marker='\n#[cfg(kani)] #[path="NBO_native.rs"] mod NBO_native;\n'
 registration=''.join(difflib.unified_diff(base.splitlines(True),(base+marker).splitlines(True),fromfile='a/'+name,tofile='b/'+name))
 out={}
 for a,s in sources.items():
  patch=registration+''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBO_native.rs'))
  (E/(a+'-harness.patch')).write_text(patch)
  out[a]={'harness_sha256':hashlib.sha256(s.encode()).hexdigest(),'patch_sha256':hashlib.sha256(patch.encode()).hexdigest()}
 (E/'NBO_NATIVE_SOURCES.json').write_text(json.dumps(out,indent=2)+'\n')
 print('Recovered patch-only source snapshots',len(out))
