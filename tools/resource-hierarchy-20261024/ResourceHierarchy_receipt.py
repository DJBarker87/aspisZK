"""Bounded local audit receipt. Child is offline and nonmutating."""
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=ROOT/'evidence/resource-hierarchy-20261024'
def pin(p):
    raw=p.read_bytes();return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))
def main():
    label=sys.argv[1]
    assert label.replace('-','').isalnum()
    target=sys.argv[2] if len(sys.argv)>2 else 'audit'
    assert target in ('audit','sources')
    command=[sys.executable,'-B',str(HERE/('ResourceHierarchy_'+target+'.py'))]
    start=time.monotonic()
    with (OUT/(label+'.json')).open('x') as log,(OUT/(label+'.log')).open('x') as err:
        child=subprocess.Popen(command,cwd=ROOT,stdout=log,stderr=err)
        _,status,usage=os.wait4(child.pid,0);exitcode=os.waitstatus_to_exitcode(status);child.returncode=exitcode
    rss=usage.ru_maxrss if platform.system()=='Darwin' else usage.ru_maxrss*1024
    receipt=dict(command=command,exit=exitcode,wall_seconds=time.monotonic()-start,peak_rss_bytes=rss,swap=usage.ru_nswap,
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        source_dependencies={str(p.relative_to(ROOT)):pin(p) for p in sorted(HERE.glob('*.py'))},
        interpreter=dict(path=sys.executable,version=sys.version,**pin(Path(sys.executable).resolve())),
        stdout=pin(OUT/(label+'.json')),stderr=pin(OUT/(label+'.log')),
        resource_scope='local offline Python; no host scope; <512 MiB measured requirement',
        print_axioms='N/A; formal budget ZERO')
    (OUT/(label+'-receipt.json')).write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:receipt[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap')}))
    assert rss<512*2**20
    return exitcode
if __name__=='__main__':raise SystemExit(main())
