from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCL_host as h
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files={}
for n,module in [('programs/r1-cost-probe/src/lib.rs','NCL_program'),('programs/r1-cost-probe/src/r1_pool_adapter.rs','NCL_adapter'),('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NCL_owned')]:
 s=subprocess.check_output(['git','show',F+':'+n],text=True)
 if module=='NCL_program':s='#![cfg_attr(kani,feature(allocator_api))]\n'+s+'\n#[cfg(kani)] extern crate alloc;\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NCL_copy;\n'
 s+='\n#[cfg(kani)] #[path="'+module+'.rs"] mod '+module+';\n';files[n]=s
 files[str(Path(n).parent/(module+'.rs'))]=(E/(module+'.rs')).read_text()
# Keep the exact copy patch, unchanged; native harnesses reference only its stubs.
files['NCL_gate.py']=(E/'NCL_gate.py').read_text()
h.admit('NCL_NATIVE_UPLOAD')
r=h.remote_py(f'''from pathlib import Path
import json,hashlib
b=Path({h.B!r});s=b/'NCL_src';files=json.loads({json.dumps(files)!r})
for n,data in files.items():
 p=(b/n) if n=='NCL_gate.py' else s/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.is_symlink():p.unlink()
 p.write_text(data)
print(json.dumps({{n:hashlib.sha256(data.encode()).hexdigest() for n,data in files.items()}},indent=2))
''');(E/'NCL_NATIVE_UPLOAD.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
# Retain the harness overlay as a standard patch; never change repo shipped files.
patch=[]
import difflib
for n,data in files.items():
 if n=='NCL_gate.py':continue
 try:old=subprocess.check_output(['git','show',F+':'+n],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 patch.extend(difflib.unified_diff(old.splitlines(True),data.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NCL_harness.patch').write_text(''.join(patch));print(r.stdout)
