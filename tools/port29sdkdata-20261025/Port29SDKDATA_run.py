#!/usr/bin/env python3
"""Exclusive run receipt and measured aggregate 512-MiB Python hard stop."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

T = Path(__file__).resolve().parent
E = T.parents[1] / 'evidence/port29sdkdata-20261025'
number = 1 + len(list(E.glob('Port29SDKDATA_run-*.json')))
stem = E / f'Port29SDKDATA_run-{number:03}'
cmd = ['/usr/bin/time', '-l', sys.executable, '-B', str(T / 'Port29SDKDATA_audit.py')]
receipt = dict(command=cmd, source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
               tool_sha256=hashlib.sha256((T / 'Port29SDKDATA_audit.py').read_bytes()).hexdigest(),
               memory_limit_bytes=512 * 1024**2, print_axioms='N/A: noncompiler audit', lean_charges=0)
with stem.with_suffix('.json').open('x') as f:
    json.dump(receipt, f, indent=2)
start = time.monotonic()
peak = 0
stop = None
with stem.with_suffix('.stdout.log').open('x') as out, stem.with_suffix('.time.log').open('x') as err:
    p = subprocess.Popen(cmd, stdout=out, stderr=err, start_new_session=True)
    while p.poll() is None:
        rows = [tuple(map(int, l.split())) for l in subprocess.check_output(['ps', '-axo', 'pid=,ppid=,rss='], text=True).splitlines()]
        ids = {p.pid}
        while True:
            nxt = ids | {pid for pid, ppid, rss in rows if ppid in ids}
            if nxt == ids:
                break
            ids = nxt
        rss = sum(rss * 1024 for pid, ppid, rss in rows if pid in ids)
        peak = max(peak, rss)
        if rss >= receipt['memory_limit_bytes'] or time.monotonic() - start >= 540:
            stop = 'aggregate 512-MiB memory bound' if rss >= receipt['memory_limit_bytes'] else '540-second bound'
            os.killpg(p.pid, signal.SIGKILL)
            break
        time.sleep(.1)
    code = p.wait()
receipt.update(exit_status=code, wall_seconds=time.monotonic()-start, aggregate_child_peak_rss_bytes=peak, stopped=stop)
for name in ['stdout', 'time']:
    f = stem.with_suffix('.' + name + '.log')
    receipt[name] = dict(path=str(f), sha256=hashlib.sha256(f.read_bytes()).hexdigest(), bytes=f.stat().st_size)
tim = stem.with_suffix('.time.log').read_text()
for suffix, key in [('maximum resident set size', 'peak_rss_bytes'), (' swaps', 'swaps')]:
    matches = [l for l in tim.splitlines() if l.strip().endswith(suffix.strip())]
    receipt[key] = int(matches[0].split()[0]) if matches else None
stem.with_suffix('.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
sys.exit(code)
