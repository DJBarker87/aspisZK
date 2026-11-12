#!/usr/bin/env python3
"""X2: compare emitted definition bodies of aspis_statement and aspis_core functions between the Pool emission and the
freeze emission (frz-emit/frza: scopes s, d, c; overflow checks ON there), at the same overflow setting. Reads only.
A definition is the text of its doc block after the doc comment (the `def` and every loop body and closure the
emitter puts under the same Rust name are taken together). Normalisation, applied to both sides:
  - the namespace prefixes AspisX2off/AspisX2on/AspisFRZfrza?, AspisX2., AspisTP3stmt., AspisTP3core., AspisTP2g.;
  - the crate prefixes aspis_statement. and aspis_core. (the freeze scopes emit their own crate without one);
  - the shim module names AspisTPNewLib./AspisXPNewLib./AspisTP2NewLib. -> SHIM.;
  - the name attributes rust_fun "..." / rust_const "..." / rust_type "..." that the emitter attaches only to
    non-local items (an attribute list left empty is removed);
  - all whitespace runs -> one space.
usage: fv_x2_compare.py <pool Funs.lean> <out.tsv> <frza Funs.lean>..."""
import collections, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'aspis-freeze-20261112' / 'host'))
import fv_frz_emit_run as FRZ
def defs(path, crate_filter):
    L = Path(path).read_text().split('\n'); out = collections.defaultdict(list)
    for b in FRZ.blocks(path):
        r = b['rust']
        if not r.startswith(crate_filter): continue
        own = r if b['loop'] else FRZ.owner(r)
        body = '\n'.join(L[b['first'] - 1:b['last']]); body = re.sub(r'(?s)^/--.*?-/\n', '', body)
        out[own].append(body)
    return out
def norm(t):
    t = re.sub(r'\bAspis(X2(off|on)?|FRZfrza[a-z]|TP3stmt|TP3core|TP2g)\.', '', t)
    t = re.sub(r'\b(aspis_statement|aspis_core)\.', '', t)
    t = re.sub(r'\bAspis(TP|XP|TP2)NewLib\.', 'SHIM.', t)
    t = re.sub(r',?\s*rust_(fun|const|type|trait|trait_impl)\s+"[^"]*"(\s*\([^)]*\))?', '', t)
    t = re.sub(r'@\[\s*,?\s*\]', '', t); t = re.sub(r'@\[\s*,\s*', '@[', t)
    return ' '.join(t.split())
def main():
    pool = Path(sys.argv[1]); out = sys.argv[2]; refs = sys.argv[3:]
    mine = {**defs(pool, 'aspis_statement::'), **defs(pool, 'aspis_core::')}
    theirs = {}
    for p in refs:
        for crate in ('aspis_statement::', 'aspis_core::'):
            for k, v in defs(p, crate).items(): theirs.setdefault(k, (Path(p).name, v))
    rows = []; n = collections.Counter()
    for k in sorted(mine):
        if k not in theirs: continue
        a = norm('\n'.join(mine[k])); src, tv = theirs[k]; b = norm('\n'.join(tv))
        st = 'identical' if a == b else 'different'
        note = ''
        if st == 'different':
            i = next((j for j in range(min(len(a), len(b))) if a[j] != b[j]), min(len(a), len(b)))
            note = 'first difference at normalised char %d: ours ...%s... | freeze ...%s...' % (i, a[max(0, i - 40):i + 60], b[max(0, i - 40):i + 60])
        n[st] += 1; rows.append((k, src, st, note))
    with open(out, 'w') as f:
        f.write('rust_path\tfreeze_module\tbody\tnote\n')
        for r in rows: f.write('\t'.join(x.replace('\t', ' ') for x in r) + '\n')
    print(dict(n), 'in both:', len(rows), 'ours only:', len([k for k in mine if k not in theirs]))

if __name__ == '__main__': main()
