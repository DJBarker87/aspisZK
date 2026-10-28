from pathlib import Path
import subprocess,json,hashlib,shlex
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-native-prepare4-20261028'
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
assert hashlib.sha256(patch.encode()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
x=dict(B=B,patch=patch,pins=json.loads((E/'NCA_SOURCE.json').read_text()))
code=r"""from pathlib import Path
import json,subprocess,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);s=b/'NCA_src'
with (b/'NCA_COPY-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NCA_COPY-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NCA_COPY-reservation.json').read_text());assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
q=s/'KMX_stubs.rs';assert not q.exists()
r=subprocess.run(['git','apply','--unsafe-paths','-'],cwd=s,input=x['patch'],text=True,capture_output=True);assert r.returncode==0,r.stderr
p=s/'crates/aspis-r1-cost-probe/src/lib.rs';text=p.read_text();assert p.is_symlink();p.unlink();p.write_text('#![cfg_attr(kani, feature(allocator_api))]\n'+text)
for p in [p,q]:x['pins']['source_sha256'][str(p.relative_to(s))]=hashlib.sha256(p.read_bytes()).hexdigest()
print(json.dumps(dict(source=x['pins'],reservation=a,patch_sha256=hashlib.sha256(x['patch'].encode()).hexdigest())))
""".replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NCA_COPY_SETUP.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
v=json.loads(r.stdout);(E/'NCA_SOURCE.json').write_text(json.dumps(v['source'],indent=2)+'\n');(E/'NCA_COPY_IMPORT.json').write_text(json.dumps({k:v[k] for k in ['reservation','patch_sha256']},indent=2)+'\n')
