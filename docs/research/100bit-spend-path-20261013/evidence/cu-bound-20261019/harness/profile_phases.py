#!/usr/bin/env python3
"""Step 4: per-phase CU from cu-profiling logs (r1:<phase> followed by
'Program consumption: N units remaining'). Emits per-phase min/max per
(kind, split, transaction) group."""
import json, re, sys, collections
from pathlib import Path
root = Path(sys.argv[1]); out = {}
rows = collections.defaultdict(lambda: collections.defaultdict(list))
for ev in sorted(root.glob('runs/*/evidence.json')):
    d = json.loads(ev.read_text()); e = d['execution']; label = ev.parent.name
    split = (e.get('cu_bound_inputs') or {}).get('split', 10); kind = 'transfer' if 'transfer' in label else 'withdrawal'
    for tx, logs in [('stage1', e['stage1_logs']), ('stage2', e['logs'])]:
        marks = []; name = None
        for l in logs:
            m = re.search(r'Program log: (r1:[\w:-]+)', l)
            if m: name = m[1]; continue
            m = re.search(r'Program consumption: (\d+) units remaining', l)
            if m and name: marks.append((name, int(m[1]))); name = None
        # name each mark by occurrence; delta = previous remaining - this remaining
        seen = collections.Counter(); prev = None
        for n, rem in marks:
            seen[n] += 1; key = n if seen[n] == 1 else f'{n}#{seen[n]}'
            if prev is not None: rows[(kind, split, tx)][key].append(prev - rem)
            prev = rem
for g, ph in rows.items():
    out['/'.join(map(str, g))] = {k: dict(min=min(v), max=max(v), n=len(v), varies=max(v) != min(v)) for k, v in ph.items()}
json.dump(out, open(sys.argv[2], 'w'), indent=1)
for g, ph in out.items():
    var = {k: v['max'] - v['min'] for k, v in ph.items() if v['varies']}
    print(g, 'phases', len(ph), 'varying', len(var), 'sum of ranges', sum(var.values()))
    for k, r in sorted(var.items(), key=lambda kv: -kv[1])[:12]: print('   ', k, r)
