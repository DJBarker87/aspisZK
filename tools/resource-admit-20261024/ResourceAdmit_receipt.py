"""Exclusive local receipt for the new actual-trace audit; never runs a host job."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from ResourceAdmit_sources import bundle,digest
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=ROOT/'evidence/resource-admit-20261024'

def main():
    label=sys.argv[1] if len(sys.argv)>1 else 'actual-audit'
    if not label.replace('-','').isalnum():raise ValueError('invalid label')
    command=[sys.executable,'-B',str(HERE/'ResourceAdmit_audit.py')]
    inputs={p.name:digest(p.read_bytes()) for p in sorted(OUT.iterdir()) if p.is_file()}
    start=time.monotonic()
    with (OUT/(label+'.log')).open('x') as log:
        child=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,cwd=ROOT)
        _,status,usage=os.wait4(child.pid,0)
        code=os.waitstatus_to_exitcode(status);child.returncode=code
    receipt=dict(command=command,exit=code,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=usage.ru_nswap,
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        sources={p.name:digest(p.read_bytes()) for p in sorted(HERE.glob('ResourceAdmit_*.py'))},
        dependencies={k:{f:v[f] for f in ('revision','path','sha256','size')} for k,v in bundle().items()},
        interpreter=dict(path=sys.executable,version=sys.version,**digest(Path(sys.executable).resolve().read_bytes())),
        inputs=inputs,output=digest((OUT/(label+'.log')).read_bytes()),print_axioms='N/A; formal budget ZERO')
    with (OUT/(label+'-receipt.json')).open('x') as out:json.dump(receipt,out,sort_keys=True,indent=2);out.write(chr(10))
    return code
if __name__=='__main__':raise SystemExit(main())
