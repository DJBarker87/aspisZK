#!/usr/bin/env python3
"""Arm details of given branch addresses: per arm L, S, L_dag, loops (header, W, nodes), callees.
usage: site_detail.py <analysis dir> <role> addr..."""
import json, sys, re
A, role = sys.argv[1:3]
d = json.load(open(f'{A}/{role}.json'))
by = {b.get('addr'): (i, b) for i, b in enumerate(d['branches'])}
for a in sys.argv[3:]:
    i, b = by[a]
    cs = sorted({(t['counts'][i], t['taken'][i]) for t in d['traces']})
    print(a, re.sub(r'17h[0-9a-f]{16}E', '', b['function'])[-60:], b['cls'], 'join', b['join'], 'count/taken', cs[:3], '...', cs[-2:])
    for nm, arm in zip('ft', b['arms']):
        print('   ', nm, {k: (v if not isinstance(v, list) else v[:6]) for k, v in arm.items() if k != 'syscalls'}, arm['syscalls'])
