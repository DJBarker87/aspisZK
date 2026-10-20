#!/usr/bin/env python3
"""Print the largest residual sites of one role/variant with source lines.
usage: show_top.py <analysis dir> <role> <variant json> [rule] [n]"""
import json, sys, re
A, role, V = sys.argv[1:4]; rule = sys.argv[4] if len(sys.argv) > 4 else None; n = int(sys.argv[5]) if len(sys.argv) > 5 else 40
lines = json.load(open(f'{A}/lines-{role}.json'))
for e in json.load(open(f'{A}/sites-per-variant.json')):
    if e['role'] != role or json.dumps(e['variant']) != V: continue
    ss = sorted([s for s in e['sites'] if s['residual'] and (rule is None or s['rule'] == rule)], key=lambda s: -s['residual'])
    print('total', sum(s['residual'] for s in ss), 'sites', len(ss))
    for s in ss[:n]:
        fr = lines.get(s['addr'], {}).get('frames') or []
        src = ' <- '.join(f"{f[1].split('/src/')[-1] if '/src/' in f[1] else f[1]}" for f in fr[:4] if 'rust/library' not in f[1] and '.cargo' not in f[1]) or (fr[0][1] if fr else 'unmapped')
        print(s['residual'], s['rule'], s['addr'], re.sub(r'17h[0-9a-f]{16}E', '', s['function'])[-60:], 'cw', s['count_w'], 'tw', s['taken_w'], 'L', s['arms_longest'], 'S', s['arms_shortest'], s['notes'], s.get('counted_arm_syscalls', ''), '|', src)
