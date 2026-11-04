from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent
code=r'''
from pathlib import Path
import json,lzma,hashlib,sys
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata3-20261104')
files={str(p.relative_to(b)):p.read_text() for p in [b/'NFV_EXTRACTION_PINS.json',b/'NFV_ref/Cargo.lock',*[q for q in (b/'NFV_extracted').rglob('*') if q.is_file()]]}
p=b/'NFV_request.llbc';llbc=p.read_bytes() if p.exists() else None
out=dict(files=files,llbc_sha256=hashlib.sha256(llbc).hexdigest() if llbc else None,llbc_size=len(llbc) if llbc else 0)
if llbc:out['llbc']=llbc.decode()
sys.stdout.buffer.write(lzma.compress(json.dumps(out,sort_keys=True).encode(),preset=6))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code.encode(),capture_output=True)
assert r.returncode==0,r.stderr
raw=lzma.decompress(r.stdout);d=json.loads(raw)
(E/'NFV_EXTRACTION_ARTIFACTS.json.xz').write_bytes(r.stdout);(E/'NFV_EXTRACTION_ARTIFACTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NFV_EXTRACTION_STATUS.json').write_text(json.dumps(dict(artifacts='NFV_EXTRACTION_ARTIFACTS.json.xz',files={n:dict(sha256=hashlib.sha256(t.encode()).hexdigest(),bytes=len(t.encode())) for n,t in d['files'].items()},llbc_sha256=d['llbc_sha256'],llbc_size=d['llbc_size'],status='Aeneas exit2 Unreachable in InterpAbs.ml1955; payment-branch abstraction merge at src/lib.rs12:18-18:9; no model closure; one extraction allocation consumed',receipt='NFV_E001/receipt.json'),indent=1)+'\n')
print(json.dumps(dict(files=len(d['files']),llbc_bytes=d['llbc_size'],compressed_bytes=len(r.stdout))))
