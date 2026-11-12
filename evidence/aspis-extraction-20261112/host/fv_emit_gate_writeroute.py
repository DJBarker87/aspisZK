#!/usr/bin/env python3
"""X7 gate (iv): the account write route. The only callers of `try_borrow_mut_data`, `try_borrow_mut_lamports`,
`RefCell::borrow_mut` and `RefMut` deref-mut in Aspis code are the write-boundary functions.
  LLBC side: X1b's fv_x1b_writecalls.py (unchanged) on each program LLBC; first on the planted positive (X1's rw2b
    LLBC, where the three lifecycle handlers call try_borrow_mut_data and RefMut::deref_mut), which must list calls.
    The boundaries are opaque by name and have no body in the LLBC, so the expected list is empty.
  Source side: every `try_borrow_mut_data`, `try_borrow_mut_lamports`, `borrow_mut(` and `deref_mut(` in the
    program's Aspis crates outside comments. For each: whether the deployed build compiles the line on the host
    target (what Charon translates) and on SBF (fv_emit_cfg.py with the resolved features of the crate in that
    program's build), the innermost LLBC function whose span holds the line, and the enclosing `fn` of the source.
    A site compiled on either target fails when it lies in a function the LLBC holds with a body and is not a write
    boundary; a site in a write-boundary function or in test code, or compiled out at the deployed features, or in
    no function of the LLBC (not reached from the root), is listed with that reason.
  Agreement: the set of reached non-boundary callers on the source side equals the set of LLBC callers (both empty).
Reads only.
usage: fv_emit_gate_writeroute.py <planted out.llbc> <tree> <run dir> <out dir> <program config.json>...
  (LLBC <run>/<program>/charon/out.llbc; features <run>/tree/<program>-host-pkgfeatures.txt, -sbf-pkgfeatures.txt)"""
import json, re, subprocess, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_x1b_llbc import LLBC
from fv_emit_lean import rel
import fv_emit_cfg as C
B = Path(__file__).resolve().parent
planted, tree, run, out = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4])
out.mkdir(parents=True, exist_ok=True)


def writecalls(llbc):
    r = subprocess.run([sys.executable, '-I', str(B / 'fv_x1b_writecalls.py'), llbc], capture_output=True, text=True)
    rows = [l for l in r.stdout.splitlines()[1:] if l.strip() and not l.startswith('#')]
    return r.returncode, r.stdout, rows


def spans_of(llbc):
    g = LLBC(llbc)
    sp = []
    for i, f in g.fun.items():
        s = f['item_meta']['span']; s = s.get('Untagged', s)
        if 'Deduplicated' in s: s = g.HC.get(s['Deduplicated'], s)
        if 'Value' in s: s = s['Value'][1]
        s = s.get('data', s)
        sp.append((rel(g.files.get(s.get('file_id'), '')), (s.get('beg') or {}).get('line') or 0, (s.get('end') or {}).get('line') or 0, g.name[i], i in g.direct))
    return sp


ok = True
rc, txt, rows = writecalls(planted)
(out / 'writecalls-planted.tsv').write_text(txt)
print('planted positive (%s): %s %d call(s) from %s' % (planted, 'fires,' if rows else 'DOES NOT FIRE,', len(rows), ', '.join(sorted({r.split('\t')[0] for r in rows}))))
ok &= bool(rows)
PAT = re.compile(r'try_borrow_mut_data|try_borrow_mut_lamports|\bborrow_mut\s*\(|\bderef_mut\s*\(')
for cp in sys.argv[5:]:
    cfg = json.loads(Path(cp).read_text())
    label = cfg['program']
    llbc = str(run / label / 'charon' / 'out.llbc')
    bnd = {w.split('.')[-1] for w in cfg['write_boundaries']}
    hf, sf = C.features(run / 'tree' / ('%s-host-pkgfeatures.txt' % label)), C.features(run / 'tree' / ('%s-sbf-pkgfeatures.txt' % label))
    rc, txt, rows = writecalls(llbc)
    (out / ('writecalls-%s.tsv' % label)).write_text(txt)
    llbc_callers = {r.split('\t')[0] for r in rows}
    print('%s LLBC (fv_x1b_writecalls.py): %d call(s)%s' % (label, len(rows), (' from ' + ', '.join(sorted(llbc_callers))) if rows else ''))
    ok &= rc == 0 and not llbc_callers
    spans = spans_of(llbc)
    src_reached = set()
    for pkg, d in zip(cfg['packages'], cfg['crate_dirs']):
        fh, fs = C.compiled_files(tree, d, hf.get(pkg, set()), 'host'), C.compiled_files(tree, d, sf.get(pkg, set()), 'sbf')
        for p in sorted((tree / d / 'src').rglob('*.rs')) + sorted(tree / x for x in (fh | fs) if not x.startswith(d + '/')):
            text = p.read_text(errors='replace')
            lines = text.split('\n')
            bl = C.blank(text).split('\n')
            ih, isb = C.inactive(text, hf.get(pkg, set()), 'host'), C.inactive(text, sf.get(pkg, set()), 'sbf')
            rp = str(p.relative_to(tree))
            for k, l in enumerate(bl):
                if not PAT.search(l):
                    continue
                ln = k + 1
                on_h, on_s = C.compiled(ih, ln) and rp in fh, C.compiled(isb, ln) and rp in fs
                inside = sorted([(b - a, n, body) for f, a, b, n, body in spans if f == rp and a <= ln <= b])
                fn = None
                for j in range(k, -1, -1):
                    m = re.search(r'\bfn\s+([A-Za-z_][A-Za-z0-9_]*)', bl[j])
                    if m: fn = m.group(1); break
                where = 'host %s, SBF %s' % ('compiled' if on_h else 'compiled out', 'compiled' if on_s else 'compiled out')
                if not on_h and not on_s:
                    v = 'compiled out at the deployed features'
                elif fn in bnd:
                    v = 'write boundary %s (opaque by name)' % fn
                elif inside and inside[0][2]:
                    v = 'FAIL: in %s, which the LLBC holds with a body' % inside[0][1]
                    src_reached.add(inside[0][1]); ok = False
                elif inside:
                    v = 'in %s, bodiless in the LLBC' % inside[0][1]
                else:
                    v = 'not reached from the root (no function of the LLBC holds the line)'
                print('  %s source %s:%d fn %s (%s): %s' % (label, rp, ln, fn, where, v))
    agree = src_reached == llbc_callers
    print('  %s agreement (source: reached non-boundary callers %s; LLBC callers %s): %s' % (label, sorted(src_reached) or 'none', sorted(llbc_callers) or 'none', 'agree' if agree else 'DISAGREE'))
    ok &= agree
print('# custom cfg flags met (taken as unset): %s' % (', '.join(sorted(C.CUSTOM_FLAGS)) or 'none'))
print('gate (iv) account write route: %s' % ('pass' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
