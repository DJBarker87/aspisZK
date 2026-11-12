#!/usr/bin/env python3
"""X7 gate (iii): no write through a reversed mutable iterator. Runs X1b's fv_x1b_mutiter.py (unchanged; the Aspis
functions whose LLBC body calls both a reversing adapter and a mutable slice iterator) first on the planted positive
(X1b's control crate x1b_probe_m: `rev_write`, `rev_write_slice`, whose emitted loop bodies drop the write), which must
list at least those two functions, then on each program LLBC, which must list none. Also the reversed-mutable-iterator
source search of the workers' runners over the given crate directories (sites are listed for reading; a site inside
a function that the LLBC reaches fails the gate). Reads only.
usage: fv_emit_gate_mutiter.py <planted out.llbc> <tree> <out dir> <label>=<out.llbc>[,<crate dir>...] ...
   e.g. verifier=/.../charon/out.llbc,programs/r1-cost-probe,crates/aspis-core"""
import re, subprocess, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_x1b_llbc import LLBC
from fv_emit_lean import rel
B = Path(__file__).resolve().parent
planted, tree, out = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
out.mkdir(parents=True, exist_ok=True)
def run(llbc, *pre):
    r = subprocess.run([sys.executable, '-I', str(B / 'fv_x1b_mutiter.py'), llbc] + list(pre), capture_output=True, text=True)
    rows = [l for l in r.stdout.splitlines()[1:] if l.strip()]
    return r.returncode, r.stdout, rows
ok = True
rc, txt, rows = run(planted, 'x1b_probe_m')
(out / 'mutiter-planted.tsv').write_text(txt)
fired = {l.split('\t')[0] for l in rows}
need = {'x1b_probe_m::rev_write', 'x1b_probe_m::rev_write_slice'}
print('planted positive (%s): %s listed: %s' % (planted, 'fires,' if need <= fired else 'DOES NOT FIRE,', ', '.join(sorted(fired)) or 'none'))
ok &= need <= fired and rc == 0
PAT = re.compile(r'\b(iter_mut|chunks_mut|chunks_exact_mut|rchunks_mut|rchunks_exact_mut|split_at_mut|values_mut|as_mut_slice)\s*\([^;{}]*?\)\s*(?:\.\s*\w+\s*\([^;{}]*?\)\s*)*\.\s*rev\s*\(\s*\)')
for spec in sys.argv[4:]:
    label, rest = spec.split('=', 1)
    parts = rest.split(',')
    llbc, dirs = parts[0], parts[1:]
    rc, txt, rows = run(llbc)
    (out / ('mutiter-%s.tsv' % label)).write_text(txt)
    print('%s LLBC: %d function(s) with both a reversing adapter and a mutable slice iterator%s' % (label, len(rows), (': ' + '; '.join(r.split('\t')[0] for r in rows)) if rows else ''))
    ok &= rc == 0 and not rows
    g = LLBC(llbc)
    spans = []
    for i, f in g.fun.items():
        s = f['item_meta']['span']; s = s.get('Untagged', s)
        if 'Deduplicated' in s: s = g.HC.get(s['Deduplicated'], s)
        if 'Value' in s: s = s['Value'][1]
        s = s.get('data', s)
        spans.append((rel(g.files.get(s.get('file_id'), '')), (s.get('beg') or {}).get('line') or 0, (s.get('end') or {}).get('line') or 0, g.name[i]))
    for d in dirs:
        for p in sorted((tree / d).rglob('*.rs')):
            t = p.read_text(errors='replace')
            for m in PAT.finditer(t):
                ln = t.count('\n', 0, m.start()) + 1
                rp = str(p.relative_to(tree))
                inside = [n for f, a, b, n in spans if f == rp and a <= ln <= b]
                print('  %s source site %s:%d %s' % (label, rp, ln, ('FAIL: inside reached function ' + ', '.join(inside)) if inside else 'not inside any function of the LLBC'))
                ok &= not inside
print('gate (iii) reversed mutable iterator: %s' % ('pass' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
