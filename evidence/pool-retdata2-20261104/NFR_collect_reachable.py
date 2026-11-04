"""Read-only recovery of raw-audit reached-name lists and binary/object pins."""
from pathlib import Path
import subprocess,lzma,json,hashlib
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,lzma,sys,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata2-20261104')
files={p.name:p.read_text() for p in b.glob('NEP_*_REACHABLE.txt')}
pins={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in [b/'NFO_native/NFR_Driver',b/'NFR_B_objects/NFR_WALKER.olean',b/'NFR_B_objects/NFR_MemoryLimit.olean']}
raw=json.dumps(dict(files=files,pins=pins),sort_keys=True).encode()
sys.stdout.buffer.write(lzma.compress(raw,preset=6))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code.encode(),capture_output=True)
assert r.returncode==0,r.stderr
raw=lzma.decompress(r.stdout)
(E/'NFR_AUDIT_ARTIFACTS.json.xz').write_bytes(r.stdout)
(E/'NFR_AUDIT_ARTIFACTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print('Retained',len(json.loads(raw)['files']),'reachable lists, compressed bytes',len(r.stdout))
