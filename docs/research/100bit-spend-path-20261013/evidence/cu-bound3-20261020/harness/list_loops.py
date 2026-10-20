#!/usr/bin/env python3
"""Unique loops (SCC headers) inside the arms of executed cyclic-class branches, per role.
usage: list_loops.py <analysis dir> <role> <out addrs.json>"""
import json, sys, re, collections
A, role, OUT = sys.argv[1:4]
d = json.load(open(f'{A}/{role}.json'))
loops = collections.OrderedDict()
for b in d['branches']:
    if 'arms' not in b or b['cls'] == 'acyclic': continue
    for arm in b['arms']:
        for l in arm.get('loops') or []:
            e = loops.setdefault(l['header'], dict(header=l['header'], W=l['W'], nodes=l['nodes'], function=b['function'], sites=set()))
            e['W'] = max(e['W'], l['W']); e['sites'].add(b['addr'])
json.dump(list(loops), open(OUT, 'w'))
for h, e in loops.items():
    print(role, h, e['W'], e['nodes'], len(e['sites']), re.sub(r'17h[0-9a-f]{16}E', '', e['function'])[-60:])
