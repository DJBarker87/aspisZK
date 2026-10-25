"""One allocated launch; local owned-process metadata only. No retry."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import selectors
import signal
import subprocess
import sys
import time

E = Path(__file__).absolute().parent
COMMAND = ['python3', '-I', '-B', '/Users/dominic/ZK/.worktrees/cx-lean-host-probe/tools/lean-host-probe-20261025/transport.py']
LIMIT = 512 * 1024 * 1024
CAP = 1024 * 1024

def durable(name, obj):
    with (E/name).open('x') as f:
        json.dump(obj, f, indent=2, sort_keys=True); f.write('\n'); f.flush(); os.fsync(f.fileno())
    fd = os.open(E, os.O_RDONLY); os.fsync(fd); os.close(fd)

def meta(pid):
    r = subprocess.run(['/bin/ps', '-p', str(pid), '-o', 'pid=,uid=,ppid=,pgid=,rss=,lstart='], capture_output=True, timeout=1)
    s = r.stdout.decode().strip().split(None, 5)
    if len(s) != 6: return None
    return dict(zip(('pid','uid','ppid','pgid','rss_bytes','birth'), [int(s[0]), int(s[1]), int(s[2]), int(s[3]), int(s[4])*1024, s[5]]))

def snapshot(root):
    rows, todo, seen = [], [root], set()
    while todo:
        pid = todo.pop()
        if pid in seen: continue
        seen.add(pid)
        m = meta(pid)
        if m is None: continue
        if m['uid'] != os.getuid() or (pid != root and m['pgid'] != root):
            raise RuntimeError('owned tree identity mismatch')
        rows.append(m)
        r = subprocess.run(['/usr/bin/pgrep', '-P', str(pid)], capture_output=True, timeout=1)
        if r.returncode not in (0,1): raise RuntimeError('child discovery failed')
        todo.extend(int(x) for x in r.stdout.split())
    own = meta(os.getpid())
    if own is None: raise RuntimeError('wrapper metadata unavailable')
    return rows + [own]

def same(a,b):
    return b is not None and all(a[k] == b[k] for k in ('pid','uid','ppid','pgid','birth'))

if __name__ == '__main__':
    start = time.monotonic()
    durable('outer-charge.json', {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'local': datetime.datetime.now().astimezone().isoformat(), 'command': COMMAND, 'allocation': 'exclusive ONE action; prep/spawn/connect uncertainty spends allocation', 'source_revision': subprocess.check_output(['git','rev-parse','HEAD'], text=True).strip(), 'wrapper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'rss_limit_bytes': LIMIT, 'wall_limit_seconds':25, 'retry':False, 'axioms':'N/A'})
    child = None; samples = []; reason = None; out = bytearray(); err = bytearray(); error = None; controlled = []
    try:
        child = subprocess.Popen(COMMAND, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        with selectors.DefaultSelector() as sel:
            for stream,tag in ((child.stdout,'stdout'),(child.stderr,'stderr')):
                os.set_blocking(stream.fileno(),False); sel.register(stream,selectors.EVENT_READ,tag)
            while sel.get_map() or child.poll() is None:
                rows = snapshot(child.pid)
                sample = {'elapsed_seconds':time.monotonic()-start,'processes':rows,'aggregate_rss_bytes':sum(x['rss_bytes'] for x in rows)}
                samples.append(sample)
                if reason is None and (sample['aggregate_rss_bytes'] >= LIMIT or sample['elapsed_seconds'] >= 25):
                    reason = '512MiB sampled aggregate ceiling' if sample['aggregate_rss_bytes'] >= LIMIT else '25 second local deadline'
                    durable('control-reason.json',{'reason':reason,'last_sample':sample,'remote_closure':'unknown'})
                    # Verify each owned identity immediately before control; never use a group kill.
                    for m in sorted(rows,key=lambda x:x['pid']==child.pid):
                        if m['pid'] != os.getpid() and m['pgid'] == child.pid and same(m,meta(m['pid'])):
                            os.kill(m['pid'],signal.SIGKILL); controlled.append(m)
                for key,_ in sel.select(0.05):
                    b = os.read(key.fd,65536)
                    if not b: sel.unregister(key.fileobj)
                    elif len(out)+len(err)+len(b) <= CAP: (out if key.data=='stdout' else err).extend(b)
                    else: raise RuntimeError('outer combined output cap exceeded')
            child.wait()
    except BaseException as e:
        error = repr(e)
        # Preserve uncertainty; do not retry launch or make unverified process-control calls.
        durable('outer-exception.json',{'error':error,'last_sample':samples[-1] if samples else None,'child_poll':None if child is None else child.poll(),'control_unresolved':child is not None and child.poll() is None})
        if child is not None and child.poll() is None:
            while child.poll() is None:
                rows = snapshot(child.pid)
                durable('exception-control-reason.json',{'reason':'monitor exception requires owned control','error':error,'processes':rows,'remote_closure':'unknown'})
                for m in rows:
                    if m['pid'] != os.getpid() and m['pgid']==child.pid and same(m,meta(m['pid'])): os.kill(m['pid'],signal.SIGKILL)
                child.wait()
    finally:
        for name,b in (('outer-stdout.txt',out),('outer-stderr.txt',err)):
            with (E/name).open('xb') as f: f.write(b); f.flush(); os.fsync(f.fileno())
        own = resource.getrusage(resource.RUSAGE_SELF); ch = resource.getrusage(resource.RUSAGE_CHILDREN)
        durable('outer-result.json',{'command':COMMAND,'exit':None if child is None else child.returncode,'wall_seconds':time.monotonic()-start,'error':error,'control_reason':reason,'controlled':controlled,'samples':samples,'sampled_aggregate_peak_rss_bytes':max((x['aggregate_rss_bytes'] for x in samples),default=0),'wrapper_peak_rss_bytes':own.ru_maxrss,'serial_child_peak_rss_bytes':ch.ru_maxrss,'self_swap_counter':own.ru_nswap,'child_swap_counter':ch.ru_nswap,'swap_bytes':'unknown','remote_rss_swap':'unobserved','sampling_limit':'discrete samples, not continuous kernel bound; transient sampler commands not captured in aggregate','axioms':'N/A: no Lean invocation','loaded_dependencies':{name:{'path':m.__file__,'sha256':hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest(),'size':Path(m.__file__).stat().st_size} for name,m in sorted(sys.modules.items()) if name != '__main__' and isinstance(getattr(m,'__file__',None),str) and Path(m.__file__).is_file()}})
    raise SystemExit(0 if child is not None and child.returncode==0 and error is None and reason is None else 1)
