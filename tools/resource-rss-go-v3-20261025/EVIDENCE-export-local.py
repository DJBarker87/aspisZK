"""Single SSH streaming driver. Exclusive evidence files, no retry."""
import os, sys, json, hashlib, time, subprocess, selectors, resource, shlex
from pathlib import Path
HERE=Path(__file__).resolve().parent
OUT=HERE.parents[1]/'evidence/resource-rss-go-v3-20261025'
payload=(HERE/'EVIDENCE-export-remote.py').read_text()
argv=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','-o','ServerAliveInterval=10','-o','ServerAliveCountMax=2','dombarker@100.108.41.90',shlex.join(['/usr/bin/python3','-I','-B','-c',payload])]
def pin(b): return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
meta=dict(argv=argv,payload_pin=pin(payload.encode()),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),base_revision='8f3c8677b5',print_axioms='N/A')
with (OUT/'EVIDENCE-command.json').open('x') as f: json.dump(meta,f,indent=2);f.write('\n')
start=time.monotonic();code=None;error=None;totals={};seq=0
# A single owned SSH PID. No process inventories or unrelated signals.
p=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
sel=selectors.DefaultSelector()
for label,stream in [('stdout',p.stdout),('stderr',p.stderr)]:
    os.set_blocking(stream.fileno(),False);sel.register(stream,selectors.EVENT_READ,label);totals[label]=0
try:
    while sel.get_map():
        if time.monotonic()-start>120: raise TimeoutError('SSH 120s deadline')
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss>512*2**20: raise MemoryError('local resident bound')
        for key,_ in sel.select(.2):
            b=os.read(key.fileobj.fileno(),512*1024)
            if not b: sel.unregister(key.fileobj);continue
            totals[key.data]+=len(b)
            if sum(totals.values())>400*2**20: raise ValueError('transport output bound')
            with (OUT/f'EVIDENCE-transport-{seq:05d}-{key.data}.bin').open('xb') as f:f.write(b)
            seq+=1
    _,status,usage=os.wait4(p.pid,0);code=os.waitstatus_to_exitcode(status);p.returncode=code
except BaseException as exc:
    error=repr(exc)
    if p.poll() is None: p.kill()
    # Killing only this Popen-owned PID cannot target an unrelated reused PID.
    try: _,status,usage=os.wait4(p.pid,0);code=os.waitstatus_to_exitcode(status);p.returncode=code
    except ChildProcessError: usage=None
finally:
    sel.close()
    own=resource.getrusage(resource.RUSAGE_SELF)
    receipt=dict(exit=code,error=error,wall_seconds=time.monotonic()-start,bytes=totals,transport_shards=seq,local_peak_rss_bytes=own.ru_maxrss,local_swap=own.ru_nswap,ssh_peak_rss_bytes=usage.ru_maxrss if usage else None,ssh_swap=usage.ru_nswap if usage else None,metrics_scope='local export driver and SSH only; not original run',print_axioms='N/A')
    with (OUT/'EVIDENCE-export-receipt.json').open('x') as f:json.dump(receipt,f,indent=2);f.write('\n')
print(json.dumps(receipt))
sys.exit(0 if code==0 and error is None else 1)
