#!/usr/bin/env python3
"""X1b gate: every bodiless declaration of one RAW Aeneas emission (`axiom` or `opaque` in any of the four files:
the two generated external templates, Types.lean, Funs.lean), classed by the Rust path its doc comment / rust_fun
attribute names. A function that fails to translate but is called by a translated body is declared as an axiom in
the external template with exit 0; this lists those. Pass condition at the end of X1b: the `aspis` rows are exactly
the account write-boundary functions.
usage: fv_x1b_aspis_axioms.py <raw dir>   (prints TSV: class, kind, lean name, rust path, file, line)"""
import re, sys
from pathlib import Path
R = Path(sys.argv[1])
ASPIS = ('aspis_core', 'aspis_statement', 'aspis_r1_cost_probe', 'aspis_r1_cost_probe_program')
def klass(rust, source):
    head = re.split(r'::|\{|<|\[|\s', rust.lstrip('{[<&\'0 '), 1)[0] if rust else ''
    if head in ASPIS or (source and re.match(r"(crates/aspis-(core|statement|r1-cost-probe)|programs/r1-cost-probe)/", source)):
        return 'aspis'
    if head in ('core', 'alloc', 'std') or (source and source.startswith('/rustc/')): return 'std'
    if head.startswith('solana') or (source and 'solana' in source): return 'sdk'
    return 'other:' + head
print('class\tkind\tlean_name\trust_path\tfile\tline')
rows = []
for f in sorted(R.glob('*.lean')):
    t = f.read_text().split('\n')
    for i, l in enumerate(t):
        m = re.match(r'^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(axiom|opaque)\s+(\S+)', l)
        if not m: continue
        j = i - 1; rust = None; source = None
        while j >= 0 and j > i - 40:
            mm = re.search(r'rust_(?:fun|type)\s+"([^"]+)"', t[j]) or (re.match(r'^\s+"([^"]+)"\]', t[j]) if '@[rust_' in t[j - 1] else None)
            if mm and rust is None: rust = mm.group(1)
            ms = re.search(r"Source: '([^']*)'", t[j])
            if ms and source is None: source = ms.group(1)
            mp = re.search(r'Name pattern: \[(.*)\]', t[j])
            if mp and rust is None: rust = mp.group(1)
            if t[j].startswith('/-- '): break
            j -= 1
        rows.append((klass(rust, source), m.group(1), m.group(2), rust or '', f.name, i + 1))
for r in sorted(rows): print('\t'.join(map(str, r)))
c = {}
for r in rows: c[r[0]] = c.get(r[0], 0) + 1
print('# counts ' + ' '.join('%s=%d' % kv for kv in sorted(c.items())), file=sys.stderr)
