#!/usr/bin/env python3
"""Aspis extraction probe: collect every XP-* slot receipt into one JSON list (exit, wall, peak RSS, cgroup peak, swap, limits). Reads only."""
import json, re
from pathlib import Path
R = Path('/home/dombarker/project-offloads/future-version-20261111/receipts'); out = []
for d in sorted(R.glob('XP-*'), key=lambda p: p.stat().st_mtime):
    g = lambda n: (d / n).read_text().strip() if (d / n).exists() else None
    t = g('time.log') or ''
    def m(pat):
        x = re.search(pat, t); return x.group(1) if x else None
    ev = g('memory_events') or ''
    out.append(dict(attempt=d.name, command=' '.join((g('argv.txt') or '').split())[:160], exit=g('exit'), wall=m(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)'),
                    peak_rss_kib=int(m(r'Maximum resident set size \(kbytes\): (\d+)') or 0), swaps=m(r'Swaps: (\d+)'), cgroup_memory_peak_bytes=int(g('cgroup_memory_peak') or 0),
                    oom_kill=(re.search(r'oom_kill (\d+)', ev) or [None, None])[1], limits=' '.join((g('limits.txt') or '').split())))
print(json.dumps(out, indent=0))
