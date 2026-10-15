#!/usr/bin/env python3
"""Run *inside* a capped build-host scope; write timing/resource JSON, no keys.

Usage: v8_state_only_cu_record.py /absolute/evidence/stem command [args...]
Set ASPIS_SOURCE_REVISION to the source commit; a dirty diff is recorded separately.
The raw .log stays on the build host. Evidence JSON is safe to copy to results.
"""
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

stem = Path(sys.argv[1]).resolve()
command = sys.argv[2:]
assert command
cgroup_rel = Path('/proc/self/cgroup').read_text().split('0::', 1)[1].strip()
cgroup = Path('/sys/fs/cgroup') / cgroup_rel.lstrip('/')
caps = {name: (cgroup / name).read_text().strip()
        for name in ('memory.high', 'memory.max', 'memory.swap.max')}
assert caps['memory.swap.max'] == '0', caps
assert caps['memory.high'] != 'max' and caps['memory.max'] != 'max', caps
assert int(caps['memory.high']) <= int(caps['memory.max']) <= 24 * 2**30, caps
stem.parent.mkdir(parents=True, exist_ok=True)
started = time.monotonic()
peak_rss = 0
stop_reason = None
with stem.with_suffix('.log').open('w') as output:
    process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                               start_new_session=True)
    while process.poll() is None:
        rss = 0
        for pid in (cgroup / 'cgroup.procs').read_text().split():
            try:
                rss += int(Path(f'/proc/{pid}/statm').read_text().split()[1]) * os.sysconf('SC_PAGE_SIZE')
            except (FileNotFoundError, ProcessLookupError):
                pass
        peak_rss = max(peak_rss, rss)
        if rss >= 24 * 2**30 or time.monotonic() - started >= 600:
            stop_reason = 'mandatory 24 GiB / ten-minute review point'
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
            break
        time.sleep(0.5)
    status = process.wait()
record = {
    'schema': 'aspis.v8-state-only-cu.resources.v1',
    'source_revision': os.environ['ASPIS_SOURCE_REVISION'],
    'host': os.uname().nodename, 'kernel': os.uname().release,
    'command': command, 'cwd': os.getcwd(), 'cgroup': str(cgroup), 'caps': caps,
    'exit_status': status, 'wall_seconds': time.monotonic() - started,
    'peak_aggregate_rss_bytes_sampled': peak_rss,
    'cgroup_memory_peak_bytes': int((cgroup / 'memory.peak').read_text()),
    'cgroup_swap_current_bytes': int((cgroup / 'memory.swap.current').read_text()),
    'child_peak_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    'stop_reason': stop_reason,
}
stem.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
sys.exit(status if status >= 0 else 128 - status)
