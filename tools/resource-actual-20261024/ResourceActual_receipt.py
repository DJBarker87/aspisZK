"""Exact local wait4 receipt for offline audit/diagnosis. Child is nonmutating."""
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/resource-actual-20261024'


def pin(p):
    raw=p.read_bytes();return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))


def main():
    target=sys.argv[1]
    assert target in ('audit','diagnose')
    command=[sys.executable,'-B',str(HERE/('ResourceActual_'+target+'.py'))]
    inputs={str(p.relative_to(ROOT)):pin(p) for p in sorted(OUT.iterdir()) if p.is_file() and not p.name.startswith(('audit','diagnose'))}
    start=time.monotonic()
    with (OUT/(target+'.log')).open('x') as log:
        child=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,cwd=ROOT)
        _,status,usage=os.wait4(child.pid,0)
        code=os.waitstatus_to_exitcode(status);child.returncode=code
    result=dict(command=command,exit=code,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss if platform.system()=='Darwin' else usage.ru_maxrss*1024,
        swap=usage.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        source_dependencies={str(p.relative_to(ROOT)):pin(p) for p in sorted(HERE.glob('*.py'))},
        reviewed_dependencies={str(p.relative_to(ROOT)):pin(p) for p in sorted((ROOT/'tools/resource-stat-20261024').rglob('*.py'))},
        inputs=inputs,output=pin(OUT/(target+'.log')),print_axioms='N/A',mode='local offline replay only; no host/consumer')
    with (OUT/(target+'-receipt.json')).open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({k:result[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap')}))
    return code

if __name__=='__main__':raise SystemExit(main())
