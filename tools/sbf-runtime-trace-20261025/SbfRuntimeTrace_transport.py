"""One authorized SSH metadata transport; terminal on any error, no retry."""
import hashlib
import json
import os
from pathlib import Path
import resource
import selectors
import subprocess
import sys
import time

ROOT=Path(__file__).parent.parent.parent
HERE=ROOT/'tools/sbf-runtime-trace-20261025'
OUT=ROOT/'evidence/sbf-runtime-trace-20261025'
ARGV=['ssh','-T','-o','BatchMode=yes','-o','ConnectionAttempts=1','-o','ConnectTimeout=15',
      'dombarker@100.108.41.90','/usr/bin/python3 -I -S -B -']
def pin(raw):return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))
def revision():return subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()

if sys.argv[1]=='register':
    sources={str(p.relative_to(ROOT)):pin(p.read_bytes()) for p in sorted(HERE.iterdir()) if p.is_file()}
    record=dict(job='SbfRuntimeTrace-20261025',source_revision=revision(),argv=ARGV,
        payload=sources['tools/sbf-runtime-trace-20261025/SbfRuntimeTrace_payload.py.txt'],sources=sources,
        limits=dict(remote_alarm_seconds=115,transport_deadline_seconds=120,output_bytes=4*2**20,
                    expected_rss_below=128*2**20,sampled_aggregate_stop_bytes=512*2**20,
                    max_files=512,max_file_bytes=16*2**20,total_file_bytes=128*2**20,max_elfs=64,symlink_hops=16),
        ownership='root uid0 files and full component chains, non-group/world-writable directories/files; same-owner symlinks; no host stage files; one tracer and one controlled import-only tracee',
        public_prefixes=['/usr/bin','/usr/lib','/usr/local/lib'],aliases=['/lib','/lib64', '/usr/lib64 (intermediate only; final original roots required)'],
        proc='own maps/status/fd plus exact unchanged guard own TGID/lineage/task children',
        guard=dict(revision='13abf7fe51',path='tools/resource-meta1g-20261025/ResourceMeta1G_guard.py',
                   pin=sources['tools/sbf-runtime-trace-20261025/SbfRuntimeTrace-guard.py.txt'],reuse='exact byte substring and globals; no semantic edits; includes both owned tracer/tracee TGIDs before release'),
        authority='job-specific finite metadata exception; no historical marker or general API adoption',
        cgroup='N/A: no scope, no inventory permitted, no reservation/admission claim',
        zero_budgets=['compiler','Lean','Cargo','Rust','Kani','backend','ELF build','root','sudo','namespace','mount','credential change','rlimit change','keys','RPC'],
        prior_failures='all six historical resource failures remain charged',
        result_policy='UNKNOWN on error; no retry, repair or second SSH; no runtime approval/producer activation')
    (OUT/'SbfRuntimeTrace-preregister.json').write_text(json.dumps(record,sort_keys=True,indent=2)+'\n')
    print(json.dumps(record['payload']))
    raise SystemExit(0)

assert sys.argv[1]=='run'
registered=json.loads((OUT/'SbfRuntimeTrace-preregister.json').read_text())
for path,expected in registered['sources'].items():
    if pin((ROOT/path).read_bytes())!=expected:raise SystemExit('local preregistered source drift; no SSH')
payload=(HERE/'SbfRuntimeTrace_payload.py.txt').read_bytes()
with (OUT/'SbfRuntimeTrace-ATTEMPTED.txt').open('x') as f:
    f.write('One metadata transport charged before launch. No retry.\n')
start=time.monotonic()
proc=subprocess.Popen(ARGV,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
sel=selectors.DefaultSelector()
for stream,kind in ((proc.stdin,'stdin'),(proc.stdout,'stdout'),(proc.stderr,'stderr')):
    os.set_blocking(stream.fileno(),False)
    sel.register(stream,selectors.EVENT_WRITE if kind=='stdin' else selectors.EVENT_READ,kind)
pos=0;data={'stdout':bytearray(),'stderr':bytearray()};terminal=None
try:
    while sel.get_map():
        if time.monotonic()-start>=120:
            terminal='transport deadline';break
        for key,mask in sel.select(min(0.1,max(0.001,120-(time.monotonic()-start)))):
            stream=key.fileobj;kind=key.data
            if kind=='stdin':
                try:n=os.write(stream.fileno(),payload[pos:pos+16384]);pos+=n
                except BrokenPipeError:terminal='payload input pipe closed';n=0;pos=len(payload)
                if pos==len(payload):sel.unregister(stream);stream.close()
            else:
                chunk=os.read(stream.fileno(),65536)
                if not chunk:sel.unregister(stream);stream.close();continue
                budget=4*2**20-sum(len(b) for b in data.values())
                data[kind].extend(chunk[:budget])
                if len(chunk)>budget:terminal='transport output bound';break
        if terminal:break
    if terminal and proc.poll() is None:proc.kill()
    code=proc.wait(timeout=max(1,120-(time.monotonic()-start)))
except BaseException as exc:
    terminal=type(exc).__name__+': '+str(exc)
    if proc.poll() is None:proc.kill()
    code=proc.wait()
finally:
    sel.close()
    for kind,b in data.items():(OUT/f'SbfRuntimeTrace-transport.{kind}').write_bytes(b)
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(argv=ARGV,argv_source='fixed ARGV; local '+('sys.orig_argv' if hasattr(sys,'orig_argv') else 'sys.argv'),local_argv=getattr(sys,'orig_argv',sys.argv),source_revision=revision(),preregister=pin((OUT/'SbfRuntimeTrace-preregister.json').read_bytes()),
             payload=pin(payload),exit=code,wall_seconds=time.monotonic()-start,terminal_error=terminal,
             stdout=pin(data['stdout']),stderr=pin(data['stderr']),stdin_bytes_sent=pos,
             local_children_peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),
             local_children_swap_operations=usage.ru_nswap,
             local_metric_scope='cumulative local child rusage includes tiny git revision reads; not host process/aggregate',
             host_metrics='see payload receipt if available; unobserved on early error',axioms='N/A')
(OUT/'SbfRuntimeTrace-transport-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
print(json.dumps(receipt,sort_keys=True))
raise SystemExit(0 if code==0 and terminal is None else 78)
