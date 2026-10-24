#!/usr/bin/env python3
"""Called under the shared flock; inventory the whole host before one scope."""
from pathlib import Path
import json, subprocess, sys
from HostAdmission import snapshot

W = Path(__file__).resolve().parent
target = sys.argv[1]
attempt = sys.argv[2] if len(sys.argv) > 2 else 'v1'
assert attempt.isalnum(), attempt
assert target in ['charon','aeneas']
report = snapshot('/sys/fs/cgroup')
G = 2**30
rows = {r['path']: r for r in report['all_cgroups']}
processes = []
for p in Path('/proc').iterdir():
    if not p.name.isdigit(): continue
    try:
        status = dict(line.split(':', 1) for line in (p/'status').read_text().splitlines() if ':' in line)
        if int(status['Tgid']) != int(p.name): continue
        cgroup = (p/'cgroup').read_text().strip()
        assert cgroup.startswith('0::'), cgroup
        path = cgroup[3:].lstrip('/') or '.'
        row = rows[path]
        if row.get('covering_capped_ancestor') is not None or row.get('memory.max', 'max') != 'max': continue
        entry = dict(pid=int(p.name), comm=(p/'comm').read_text().strip(), cgroup=path,
                     rss_bytes=int(status.get('VmRSS', '0 kB').split()[0])*1024)
        if entry['comm'].startswith('qemu'):
            argv = (p/'cmdline').read_bytes().decode().split(chr(0))
            arg = argv[argv.index('-m')+1]
            entry['guest_memory_argument'] = arg
            assert arg in ['size=4194304k', 'size=16777216k'], arg
            entry['guest_max_bytes'] = int(arg.removeprefix('size=').removesuffix('k'))*1024
        processes.append(entry)
    except FileNotFoundError:
        continue
meminfo = dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
report.update(uncapped_processes=processes, additional_bytes=2*G,
              uncapped_background_allowance_bytes=28*G,
              background_allowance_basis='Guest configured maxima <=20GiB +2GiB VM overhead +6GiB other uncapped services; observed other RSS must be <=4GiB. This is a monitored allowance, not a cgroup cap on those services.',
              available_bytes=int(meminfo['MemAvailable'].split()[0])*1024,
              shared_lock='/tmp/aspis-r0-lean.lock', target=target)
report['admitted'] = (report['reserved_bytes'] + 2*G + 28*G < 55*G
    and report['available_bytes'] >= 10*G
    and sum(p.get('guest_max_bytes',0) for p in processes) <= 20*G
    and sum(p['rss_bytes'] for p in processes if 'guest_max_bytes' not in p) <= 4*G
    and not any(p['comm'] in ['lean','rustc','cbmc','kani','z3','cargo','lake','charon','aeneas'] for p in processes))
(W/(target+'-'+attempt+'-admission.json')).write_text(json.dumps(report,indent=2)+'\n')
assert report['admitted'], 'Fresh whole-host admission refused; no build launched'
cmd = ['systemd-run','--user','--scope','-q','-p','MemoryHigh=1536M',
       '-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64',
       'python3',str(W/'extract-host.py'),target]
raise SystemExit(subprocess.call(cmd))
