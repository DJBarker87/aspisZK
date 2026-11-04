from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
old=json.loads((E.parent/'pool-retdata2-20261104/NFR_ELF_PINS.json').read_text())
code=f'''from pathlib import Path
import hashlib,json,shutil
pins={old['pins']!r}
for p in pins:
 q=Path(p['path']);p['actual_sha256']=hashlib.sha256(q.read_bytes()).hexdigest();p['size']=q.stat().st_size;p['matches']=p['actual_sha256']==p['sha256']
assert all(p['matches'] for p in pins)
print(json.dumps(dict(pins=pins,rebuilt=False,reason='No shipped repository files edited; every cfg(kani) harness and KMX application lives only in the scratch copy. Read-only final pin recheck, not a rebuild claim.',disk_free_bytes=shutil.disk_usage('/home/dombarker/project-offloads').free),indent=1))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NFV_ELF_PINS.json').write_text(r.stdout);print('Three frozen ELF hashes match')
