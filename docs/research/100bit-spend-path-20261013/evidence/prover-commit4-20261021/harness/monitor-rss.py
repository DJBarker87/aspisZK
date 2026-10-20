#!/usr/bin/env python3
"""Attach a read-only aggregate child RSS sampler to one named receipt scope."""
import json,time,sys
from pathlib import Path
name=sys.argv[1]
h=Path('/home/dombarker/project-offloads/codex-cx-prover-commit4-20261021/receipts')/name
while not (h/'time.log').exists():time.sleep(2)
cg=None
for p in Path('/proc').iterdir():
 if p.name.isdigit():
  try:
   args=(p/'cmdline').read_bytes().split(b'\0')
   if any(a.endswith(b'/harness/capped.py') for a in args) and str(h).encode() in args:
    cg=Path('/sys/fs/cgroup'+(p/'cgroup').read_text().split('0::',1)[1].strip());break
  except OSError:pass
assert cg is not None
samples=[]
while not (h/'receipt.json').exists():
 rss=0
 try:
  for pid in (cg/'cgroup.procs').read_text().split():
   try:
    for line in Path('/proc',pid,'status').read_text().splitlines():
     if line.startswith('VmRSS:'):rss+=int(line.split()[1]);break
   except OSError:pass
  samples.append(dict(unix_seconds=time.time(),aggregate_rss_kib=rss))
 except OSError:break
 time.sleep(2)
x=dict(cgroup=str(cg),sample_interval_seconds=2,sampling_start='attached after launch; peak is sampled, not a kernel RSS high-water mark',peak_sampled_aggregate_rss_kib=max((s['aggregate_rss_kib'] for s in samples),default=0),samples=samples)
(h/'rss-samples.json').write_text(json.dumps(x,indent=2)+'\n')
