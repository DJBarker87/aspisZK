#!/usr/bin/env python3
"""X7: the declarations of aspis_statement and aspis_core that occur in BOTH programs' raw emissions (same Lean name
after the namespace), and whether each emitted text is identical after normalisation: the doc comment dropped, the
namespace prefixes `AspisX1.` / `AspisX2.` removed, whitespace runs collapsed. For each that differs: the first
differing lines, and, as a hint, every `cfg` site inside the item's source lines whose value differs between the two
builds' resolved features of that crate (fv_emit_cfg.py), and the bodiless names one side calls and the other does
not. Reads only.
usage: fv_emit_shared.py <tree> <run dir> <verifier config.json> <pool config.json>   (TSV on stdout; summary last)"""
import difflib, json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_emit_lean import blocks, crate_of, item_extent, rel
import fv_emit_cfg as C

tree, run = Path(sys.argv[1]), Path(sys.argv[2])
cv, cp = json.loads(Path(sys.argv[3]).read_text()), json.loads(Path(sys.argv[4]).read_text())
fv = C.features(run / 'tree' / 'verifier-host-pkgfeatures.txt')
fp = C.features(run / 'tree' / 'pool-host-pkgfeatures.txt')
PK = {'aspis_statement': 'aspis-statement', 'aspis_core': 'aspis-core'}


def load(cfg):
    R = run / cfg['program'] / 'aeneas' / 'raw' / cfg['ns']
    out, bodiless = {}, set()
    for fn in ('Funs.lean', 'FunsExternal_Template.lean'):
        for b in blocks(R / fn):
            if b['kind'] in ('axiom', 'opaque'):
                bodiless.add(b['lean'])
            c = crate_of(b['file'], b['rust'])
            if fn == 'Funs.lean' and c in PK and b['kind']:
                t = b['text'].replace(cfg['ns'] + '.', '')
                t = re.sub(r'\s+', ' ', t).strip()
                out[b['lean'], b['label']] = (c, b, t)
    return out, bodiless


V, bv = load(cv)
Pd, bp = load(cp)
both = sorted(set(V) & set(Pd))
same = 0
print('lean_name\tlabel\tcrate\tsource\tresult\tfeature-gated sites in the item with different values\tbodiless calls on one side\tfirst difference')
for k in both:
    c, b, t1 = V[k]
    _, b2, t2 = Pd[k]
    if t1 == t2:
        same += 1
        continue
    f = rel(b['file'])
    a, z = item_extent(tree, f, b['a'], b['b'])
    sites = []
    if a:
        text = (tree / f).read_text(errors='replace')
        for line, expr, x, y, inner in C.sites(text):
            if a <= line <= z or (x <= a and z <= y and not inner):
                try:
                    ast = C.parse(expr)
                    v1, v2 = C.value(ast, fv.get(PK[c], set()), 'host'), C.value(ast, fp.get(PK[c], set()), 'host')
                except Exception:
                    v1 = v2 = None
                if v1 != v2:
                    sites.append('%d %s (verifier %s, pool %s)' % (line, expr, v1, v2))
    n1 = set(re.findall(r'[A-Za-z_][\w.]*', t1)); n2 = set(re.findall(r'[A-Za-z_][\w.]*', t2))
    bl = sorted((n1 - n2) & bv) + sorted((n2 - n1) & bp)
    d = [l for l in difflib.unified_diff(t1.split(' '), t2.split(' '), lineterm='', n=3)][2:8]
    print('\t'.join([k[0], k[1], c, '%s:%s' % (f, b['a']), 'differs', '; '.join(sites) or 'none', ', '.join(bl) or 'none', ' '.join(d)[:300]]))
print('# shared declarations %d; identical %d; different %d; only in verifier %d; only in pool %d' % (
    len(both), same, len(both) - same, len(set(V) - set(Pd)), len(set(Pd) - set(V))))
