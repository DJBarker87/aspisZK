"""Run one bounded-size local offline Python target with exact wait4 receipt."""
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=ROOT/'evidence/resource-stat-20261024'

def main():
    target=sys.argv[1]
    if target not in ('tests','audit','sources'):raise ValueError('offline target only')
    command=[sys.executable,'-B',str(HERE/('ResourceStat_'+target+'.py'))]
    hashes={str(p.relative_to(ROOT)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in sorted(HERE.rglob('*.py'))}
    start=time.monotonic()
    with (OUT/(target+'.log')).open('w') as log:
        child=subprocess.Popen(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        _,status,usage=os.wait4(child.pid,0)
        code=os.waitstatus_to_exitcode(status);child.returncode=code
    receipt=dict(target=target,command=command,exit=code,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss if platform.system()=='Darwin' else usage.ru_maxrss*1024,
        swap=usage.ru_nswap,resource_scope='local offline Python only; no host scope/reservation; expected <512MiB',
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        source_worktree_status=subprocess.check_output(['git','status','--short','--','tools/resource-stat-20261024','evidence/resource-stat-20261024'],cwd=ROOT,text=True).splitlines(),
        source_dependency_hashes=hashes,interpreter=sys.version,platform=platform.platform(),
        print_axioms='N/A; ZERO Lean/Kani/Rust/build/compiler/extraction/backend/ELF work')
    if (OUT/'input-manifest.json').exists():receipt['input_manifest_sha256']=hashlib.sha256((OUT/'input-manifest.json').read_bytes()).hexdigest()
    receipt['log_sha256']=hashlib.sha256((OUT/(target+'.log')).read_bytes()).hexdigest()
    (OUT/(target+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('target','exit','wall_seconds','peak_rss_bytes','swap')}))
    return code

if __name__=='__main__':raise SystemExit(main())
