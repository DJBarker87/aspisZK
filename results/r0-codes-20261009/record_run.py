#!/usr/bin/env python3
"""Execute INSIDE a capped systemd scope; record exact command/resources."""
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

out, revision, *command = sys.argv[1:]
cgroup = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::')[1].lstrip('/')
read = lambda name: (cgroup / name).read_text().strip()
caps = {name: read(name) for name in ['memory.high', 'memory.max', 'memory.swap.max']}
assert caps['memory.swap.max'] == '0'
assert 0 < int(caps['memory.high']) <= int(caps['memory.max']) <= 6*1024**3
started = time.monotonic()
process = subprocess.Popen(command)
peak_rss = 0
while process.poll() is None:
    # Every process in the scope, including compiler children.
    rss = 0
    for path in cgroup.rglob('cgroup.procs'):
        for pid in path.read_text().split():
            try:
                pages = int(Path(f'/proc/{pid}/statm').read_text().split()[1])
                rss += pages * os.sysconf('SC_PAGE_SIZE')
            except (OSError, IndexError, ValueError): pass
    peak_rss = max(peak_rss, rss)
    time.sleep(0.1)
status = process.wait()
result = dict(command=command, source_revision=revision, host=os.uname().nodename,
              cwd=os.getcwd(), cgroup=str(cgroup), caps=caps, exit_status=status,
              wall_seconds=time.monotonic()-started,
              peak_aggregate_rss_bytes_sampled=peak_rss,
              child_peak_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
              cgroup_memory_peak_bytes=int(read('memory.peak')),
              cgroup_swap_current_bytes=int(read('memory.swap.current')),
              cgroup_swap_peak_bytes=int(read('memory.swap.peak')) if (cgroup/'memory.swap.peak').exists() else None)
Path(out).write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2), flush=True)
sys.exit(status)
