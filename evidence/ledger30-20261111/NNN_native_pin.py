"""Seal the single job-owned optimized scan binary and immutable raw walker."""
from pathlib import Path
import subprocess,json,shlex
E=Path(__file__).resolve().parent
code="""from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNN_20261111');p=b/'NNN_native/NNN_RuntimeScan';q=b.parent/'NNM_20261111/NNM_native/NNM_ProofDriver'
def pin(p):return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
print(json.dumps(dict(scan=pin(p),raw=pin(q),scan_source_c=pin(b/'NNN_native/NNN_RuntimeScan.c'))))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3','-c',shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert x['raw']['sha256']=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
rc=json.loads((E/'NNN_L003/receipt.json').read_text());assert x['scan_source_c']['sha256']==rc['source_hashes']['NNN_native/NNN_RuntimeScan.c']
x.update(scan_link_attempt='NNN_L003',scan_uses=['NNN_L004','NNN_L009'],native_output_pin_timing='post-run read-only seal; this job has exactly one successful linker invocation and no binary replacement',optimization='leanc -O3 -rdynamic',object_sources='NNN_L003/sources/NNN_native/NNN_RuntimeScan.c')
(E/'NNN_NATIVE_BINARY_PIN.json').write_text(json.dumps(x,sort_keys=True,indent=1)+'\n');print('Optimized scan binary and unchanged raw walker sealed')
