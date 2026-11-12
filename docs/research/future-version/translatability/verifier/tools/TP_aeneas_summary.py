#!/usr/bin/env python3
"""Aspis extraction probe: per-function list of the errors in one Aeneas log. Reads only.
usage: XP_aeneas_summary.py <aeneas run> [json-out]"""
import json, re, sys
from pathlib import Path
E = Path(__file__).resolve().parent
log = re.sub(r'\x1b\[[0-9;]*m', '', (E / 'runs' / sys.argv[1] / 'aeneas.log').read_text(errors='replace'))
blocks = re.split(r'(?m)^(?=\[Error\])', log)
res = {}; last = None
for b in blocks:
    if not b.startswith('[Error]'): continue
    msg = b.split('\n', 1)[0][len('[Error] '):].strip()
    src = re.search(r"(?m)^Source: '([^']*)', lines ([0-9:\-]+)", b)
    m = re.search(r"Could not translate the (?:body of function|function signature of|function) '(.*?) because of previous error", b, re.S) or re.search(r"Ignoring the body of '(.*?)' because of previous error", msg)
    where = ('%s %s' % (src.group(1).split('/src/')[-1] if '/rustc/' not in src.group(1) and 'registry' not in src.group(1) else src.group(1).split('/')[-1], src.group(2))) if src else ''
    if m:
        fn = ' '.join(m.group(1).split())
        kind = 'signature' if 'function signature' in b else 'body'
        if msg.startswith('Ignoring the body'):
            if last: res.setdefault(fn, []).append(dict(kind='body', error=last[0], at=last[1]))
        else:
            res.setdefault(fn, []).append(dict(kind=kind, error=msg, at=where))
        last = None
    else:
        last = (msg, where)
for fn, errs in res.items():
    seen = []
    for e in errs:
        if e['error'].startswith('Internal error') and any(not x['error'].startswith('Internal error') for x in errs): continue
        if e not in seen: seen.append(e)
    res[fn] = seen
    print(fn[:150]); [print('    %s: %s  [%s]' % (e['kind'], e['error'][:110], e['at'])) for e in seen]
if len(sys.argv) > 2: json.dump(res, open(sys.argv[2], 'w'), indent=1)
