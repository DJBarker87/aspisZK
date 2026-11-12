#!/usr/bin/env python3
"""X1 item G: for every std external (axiom of FunsExternal whose Rust path starts with core::, alloc:: or std::) of one
emission run, the Aspis definitions of Funs that mention it, with the number of mentions (call sites in the Lean;
closures and loop bodies are counted for the function that owns them). Reads only.
usage: fv_x1_callers.py <run dir> <out.tsv>"""
import collections, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fv_x1_rows as R
RUN = Path(sys.argv[1]); cfg = __import__('json').loads((RUN / 'config.json').read_text()); pre = cfg['prefix']
ext = [b for b in R.blocks(RUN / 'lean-src' / (pre + 'FunsExternal.lean')) if b['kind'] == 'axiom' and b['rust'].split('::')[0] in ('core', 'alloc', 'std')]
funs = R.blocks(RUN / 'lean-src' / (pre + 'Funs.lean'))
def owner(r):
    m = re.search(r' for ([\w:]+?)::\{?closure', r)
    if m: return m.group(1)
    return re.sub(r'::\{impl core::ops::function.*$', '', r)
rows = []
for e in ext:
    nm = e['lean']; pat = re.compile(r'(?<![\w.])' + re.escape(nm) + r'(?![\w])')
    c = collections.Counter()
    for b in funs:
        body = re.sub(r'(?s)^/--.*?-/\n', '', b['body'])
        n = len(pat.findall(body))
        if n: c[owner(b['rust'])] += n
    rows.append((e['rust'], nm, sum(c.values()), '; '.join('%s x%d' % kv for kv in sorted(c.items()))))
with open(sys.argv[2], 'w') as f:
    f.write('std_external\tlean_name\tlean_mentions\tcallers (Aspis function x mentions; closures and loop bodies counted for their function)\n')
    for r in rows: f.write('\t'.join(map(str, r)) + '\n')
print(len(rows))
