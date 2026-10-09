#!/usr/bin/env python3
"""Run inside the caller's capped systemd scope, record Rust-only evidence."""
import json, os, resource, subprocess, sys, time, signal, hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
name,*command=sys.argv[1:]
source=json.loads((HERE/'semantic-source-manifest.json').read_text())
for path, expected in source['files'].items():
    assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected, path
cgroup=Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::')[1].lstrip('/')
def read(n):
    p=cgroup/n
    return p.read_text().strip() if p.exists() else None
caps={n:read(n) for n in ['memory.high','memory.max','memory.swap.max']}
assert caps['memory.swap.max']=='0' and caps['memory.max']!='max', caps
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_BUILD_JOBS='2',
         CARGO_TARGET_DIR=str(ROOT/'target'),R0_SEMANTIC_EVIDENCE_DIR=str(HERE))
start=time.monotonic(); peak=0; stopped=None
with (HERE/(name+'.log')).open('w') as log:
    child=subprocess.Popen(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    while child.poll() is None:
        rows=subprocess.check_output(['ps','-axo','pgid=,rss='],text=True)
        peak=max(peak,sum(int(r.split()[1]) for r in rows.splitlines() if int(r.split()[0])==child.pid))
        if time.monotonic()-start>540:
            stopped='nine-minute review limit'; os.killpg(child.pid,signal.SIGKILL);break
        time.sleep(.2)
    code=child.wait()
record=dict(command=command,exit_status=code,wall_seconds=time.monotonic()-start,
    peak_aggregate_rss_kib_sampled=peak,child_peak_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    cgroup=str(cgroup),caps=caps,cgroup_memory_peak=read('memory.peak'),swap_current=read('memory.swap.current'),
    swap_peak=read('memory.swap.peak'),stopped=stopped,source=source,source_hashes_verified_before_run=True,
    formal_axioms='not applicable: Rust-only, no Lean changes')
(HERE/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print('\n'.join((HERE/(name+'.log')).read_text().splitlines()[-22:]))
print(json.dumps({k:v for k,v in record.items() if k!='source'}))
sys.exit(code if code>=0 else 1)
