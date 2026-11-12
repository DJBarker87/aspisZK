#!/usr/bin/env python3
"""X1b item G: for every bodiless non-Aspis function of one LLBC (std, SDK, runtime), the Aspis functions whose body
calls it, with the file and line of each call statement (the span of the nearest enclosing statement). Closures and
loop bodies are reported under their own LLBC names. Edge rule as fv_x1b_llbc.py; spans resolved through the hash-cons
table.
usage: fv_x1b_callers.py <out.llbc> [<name regex>]   (prints TSV: callee, class, caller, file, line)"""
import re, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from fv_x1b_llbc import LLBC
g = LLBC(sys.argv[1]); flt = re.compile(sys.argv[2]) if len(sys.argv) > 2 else None
bodiless = {i for i, f in g.fun.items() if i not in g.direct}
def span_of(s):
    if not isinstance(s, dict): return None
    if 'Deduplicated' in s: s = g.HC.get(s['Deduplicated'], {})
    if isinstance(s, dict) and 'Value' in s: s = s['Value'][1]
    s = s.get('Untagged', s) if isinstance(s, dict) else s
    s = s.get('data', s) if isinstance(s, dict) else s
    return (g.files.get(s.get('file_id'), '?'), s.get('beg', {}).get('line')) if isinstance(s, dict) and 'beg' in s else None
def calls(body):
    out = set(); stack = [(body, None)]; seen = set()
    while stack:
        v, sp = stack.pop()
        if isinstance(v, list): stack.extend((w, sp) for w in v); continue
        if not isinstance(v, dict): continue
        if 'span' in v and ('kind' in v or 'content' in v):
            sp = span_of(v['span']) or sp
        for k, w in v.items():
            if k == 'Drop': continue
            if k == 'Deduplicated' and isinstance(w, int):
                if (w, sp) not in seen: seen.add((w, sp)); stack.append((g.HC.get(w), sp))
                continue
            if k == 'Regular' and isinstance(w, dict) and isinstance(w.get('kind'), dict) and isinstance(w['kind'].get('Fun'), int):
                out.add((w['kind']['Fun'], sp))
            stack.append((w, sp))
    return out
def klass(n):
    h = n.split('::')[0]
    return 'std' if h in ('core', 'alloc', 'std') else ('sdk' if h.startswith('solana') else ('aspis' if h.startswith('aspis_') else 'other'))
rows = set()
for i in g.direct:
    if not g.name[i].startswith('aspis_'): continue
    for c, sp in calls(g.fun[i]['body']):
        if c in bodiless and not g.name[c].startswith('aspis_'):
            if flt and not flt.search(g.name[c]): continue
            rows.add((g.name[c], klass(g.name[c]), g.name[i], sp[0] if sp else '?', sp[1] if sp else 0))
print('callee\tclass\tcaller\tfile\tline')
for r in sorted(rows): print('\t'.join(map(str, r)))
