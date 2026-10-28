from KNH_host import *
import base64
admit('KNH_UPLOAD')
files={p.name:p.read_text() for p in E.glob('KNH_*.rs.txt')}
files['KNH_FROZEN_Cargo.lock']=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'],text=True)
files['KNH_Cargo.toml.txt']=(E/'KNH_Cargo.toml.txt').read_text()
code='''from pathlib import Path
import json,hashlib
b=Path(%r);files=json.loads(%r)
s=b/'KNH_scratch';s.mkdir(exist_ok=True);(b/'KNH_tmp').mkdir(exist_ok=True)
for n,v in files.items():(b/n).write_text(v)
(s/'Cargo.lock').write_text(files['KNH_FROZEN_Cargo.lock'])
(s/'Cargo.toml').write_text(files['KNH_Cargo.toml.txt'])
(s/'KMX_stubs.rs').write_text(files['KNH_KMX_stubs.rs.txt'])
print(json.dumps(dict(files={n:hashlib.sha256(v.encode()).hexdigest() for n,v in files.items()},scratch=str(s))))
'''%(B,json.dumps(files))
import zlib
packed=base64.b64encode(zlib.compress(code.encode())).decode()
r=py('import base64,zlib;exec(zlib.decompress(base64.b64decode('+repr(packed)+')))');assert r.returncode==0,r.stderr;(E/'KNH_UPLOAD.json').write_text(r.stdout)
# Pin old tools without running a verifier.
r=py('''from pathlib import Path
import hashlib,json,subprocess
roots=[Path('/home/dombarker/.kani/kani-0.67.0/bin'),Path('/home/dombarker/.cargo/bin/cargo-kani')]
files={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for r in roots for p in ([r] if r.is_file() else r.iterdir()) if p.is_file()}
print(json.dumps(dict(version=subprocess.check_output(['/home/dombarker/.cargo/bin/cargo-kani','--version'],text=True),files=files),indent=2))
''');assert r.returncode==0;(E/'KNH_PINNED_BEFORE.json').write_text(r.stdout)
