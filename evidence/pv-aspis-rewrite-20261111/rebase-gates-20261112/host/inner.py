#!/usr/bin/env python3
"""Runs inside the capped scope: CGROUP_JSON STDOUT STDERR CMD...; records own cgroup peaks."""
import sys, subprocess, json, pathlib
out, so, se = sys.argv[1:4]
cmd = sys.argv[4:]
cg = pathlib.Path('/sys/fs/cgroup') / next(x.split(':', 2)[2].strip().lstrip('/')
                                           for x in open('/proc/self/cgroup').read().splitlines() if x.startswith('0:'))
with open(so, 'wb') as fo, open(se, 'wb') as fe:
    rc = subprocess.run(cmd, stdout=fo, stderr=fe).returncode
def rd(n):
    try: return (cg / n).read_text().strip()
    except Exception as e: return 'unreadable: %s' % e
pathlib.Path(out).write_text(json.dumps(dict(cgroup=str(cg), exit=rc, memory_peak=rd('memory.peak'),
    memory_swap_peak=rd('memory.swap.peak'), memory_events=rd('memory.events'), pids_peak=rd('pids.peak'),
    memory_high=rd('memory.high'), memory_max=rd('memory.max'), memory_swap_max=rd('memory.swap.max'),
    pids_max=rd('pids.max')), indent=2) + '\n')
sys.exit(rc)
