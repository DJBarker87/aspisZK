"""One local 60s coordination wait; never reads a live output or contacts host."""
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import ResourceAdmit_local as local
from ResourceAdmit_sources import digest

def main():
    command=['ps','-p','7112','-o','pid=,lstart=,command=']
    observations=[];started=time.monotonic()
    def inspect():
        start=time.monotonic();p=subprocess.run(command,text=True,capture_output=True)
        observations.append(dict(command=command,exit=p.returncode,wall_seconds=time.monotonic()-start,stdout=p.stdout,stderr=p.stderr))
        if p.returncode not in (0,1):raise RuntimeError('local ps failed')
        if p.stdout.strip():
            if local.COORD_START not in p.stdout or str(local.COORD_OUTPUT) not in p.stdout:
                raise RuntimeError('PID/start/command identity changed; stop')
            return True
        return False
    live=inspect();waited=0
    if live:
        with (local.OUT/'ResourceAdmit_WAITED').open('x') as f:f.write('one 60-second coordination wait only'+chr(10))
        start=time.monotonic();time.sleep(60);waited=time.monotonic()-start
        live=inspect()
    terminal=None
    if not live:terminal=local.coordination()
    code=78 if live else 0
    result=dict(state='WAITING' if live else 'TERMINAL_REVIEW',exit=code,
        command=[sys.executable,'-B',str(Path(__file__).resolve())],
        source_revision=local.revision(),source=digest(Path(__file__).read_bytes()),
        dependencies={p.name:digest(p.read_bytes()) for p in sorted(Path(__file__).parent.glob('ResourceAdmit_*.py'))},
        interpreter=dict(path=sys.executable,version=sys.version,**digest(Path(sys.executable).resolve().read_bytes())),
        wall_seconds=time.monotonic()-started,wait_seconds=waited,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        child_peak_rss_bytes=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        swap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,
        observations=observations,terminal=terminal,host_operations=0,admission_attempts=0,
        output_read=not live,print_axioms='N/A; formal budget ZERO')
    with (local.OUT/'ResourceAdmit-coordination.json').open('x') as out:json.dump(result,out,sort_keys=True,indent=2);out.write(chr(10))
    print(json.dumps({k:result[k] for k in ('state','exit','wait_seconds','host_operations','admission_attempts')}))
    return code
if __name__=='__main__':raise SystemExit(main())
