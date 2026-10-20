#!/usr/bin/env python3
"""Run one command inside the current (capped) scope and write a receipt.
usage: capped.py <receipt-dir> <expected-time-note> -- cmd...
Refuses to reuse an existing receipt dir (no unchanged reruns)."""
import hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
rdir = Path(sys.argv[1]); note = sys.argv[2]; assert sys.argv[3] == '--'; cmd = sys.argv[4:]
rdir.mkdir(parents=True, exist_ok=False)
cg = '/sys/fs/cgroup' + Path('/proc/self/cgroup').read_text().split('0::', 1)[1].strip()
limits = {n: Path(cg, n).read_text().strip() for n in ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max']}
assert limits['memory.swap.max'] == '0' and int(limits['memory.max']) <= 8 * 2**30, limits
start = time.monotonic()
with open(rdir / 'stdout.log', 'w') as so, open(rdir / 'stderr.log', 'w') as se:
    status = subprocess.run(['/usr/bin/time', '-v', '-o', str(rdir / 'time.log'), *cmd], stdout=so, stderr=se).returncode
wall = time.monotonic() - start
tl = (rdir / 'time.log').read_text()
m = lambda n: (int(x[1]) if (x := re.search(re.escape(n) + r':\s*(\d+)', tl)) else None)
H = Path('/home/dombarker/project-offloads/codex-cx-stage2b-20261020')
rec = dict(source_revision=os.environ.get('ASPIS_SOURCE_REVISION',(H/'source-revision.txt').read_text().strip()), source_root=os.environ['ASPIS_SOURCE_ROOT'], source_hashes={str(p.relative_to(Path(os.environ['ASPIS_SOURCE_ROOT']))):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(os.environ['ASPIS_SOURCE_ROOT'])/'crates/aspis-r1-cost-probe/src').glob('*.rs')}, command=cmd, cwd=os.getcwd(), expected_time=note, exit_status=status, wall_seconds=round(wall, 3),
           peak_rss_kib=m('Maximum resident set size (kbytes)'), swaps=m('Swaps'), cgroup=cg, limits=limits,
           cgroup_memory_peak_bytes=int(Path(cg, 'memory.peak').read_text()),
           env={k: os.environ.get(k) for k in ['CARGO_TARGET_DIR', 'CARGO_BUILD_JOBS', 'CARGO_NET_OFFLINE', 'SBF_TRACE_DIR', 'RUSTFLAGS']},
           print_axioms='N/A: no Lean compilation')
(rdir / 'receipt.json').write_text(json.dumps(rec, indent=1) + '\n')
print(json.dumps({k: rec[k] for k in ['exit_status', 'wall_seconds', 'peak_rss_kib', 'swaps']}))
sys.exit(status)
