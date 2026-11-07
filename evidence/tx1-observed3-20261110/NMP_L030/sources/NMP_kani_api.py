"""Read pinned tool APIs only; no compiler/launcher change."""
from pathlib import Path
import subprocess,json,hashlib
B=Path.cwd();paths=[]
for root in ['/home/dombarker/.kani','/home/dombarker/.cargo']:
 r=subprocess.run(['rg','--files',root],capture_output=True,text=True)
 paths += [Path(p)for p in r.stdout.splitlines()if ('/library/kani/src/'in p or '/library/kani_core/src/'in p) and p.endswith('.rs')]
rows=[]
for p in paths:
 raw=p.read_text()
 hits=[(i+1,l)for i,l in enumerate(raw.splitlines())if any(t in l for t in ['pub unsafe fn any_raw','pub fn any','pub fn havoc','pub unsafe fn havoc','is_initialized','initialize','write_bytes','any_slice','any_vec','havoc','any_raw','valid_ptr','pub unsafe fn write'])]
 if hits:rows.append(dict(path=str(p),sha256=hashlib.sha256(raw.encode()).hexdigest(),hits=hits))
(B/'NMP_KANI_API.json').write_text(json.dumps(rows,indent=1));print(json.dumps(dict(files=len(paths),matching_files=len(rows))))
