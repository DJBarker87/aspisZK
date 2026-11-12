#!/usr/bin/env python3
"""Aspis translatability pass: second set of variant trees, for choosing the form of the two rewrites that cost compute
(canonical_scan and prepared_claim). The reference R is: base tree + patch 0 (third version) + patch 1 + patch 2 with
canonical_scan left pinned + patch 3. Each variant changes one thing in R.
usage: TP_variants2.py <tree after patch 1> <R tree> <base tree> <out dir>   (run from the repository root)"""
import subprocess, sys, shutil
from pathlib import Path
U1, R, BASE, OUT = [Path(x) for x in sys.argv[1:5]]
HERE = Path(__file__).resolve().parent
src_fx = (HERE / 'TP_fntext.py').read_text().split("rep = {}")[0].replace("A, B, OUT = sys.argv[1:4]; FILES = sys.argv[4:]", "")
fx = {}; exec(compile(src_fx, 'TP_fntext_head', 'exec'), fx)
V = 'crates/aspis-r1-cost-probe/src/verifier.rs'; C = 'crates/aspis-r1-cost-probe/src/candidate.rs'
def emit(name, files, what):
    for f, t in files.items():
        p = OUT / name / f; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(t)
    print(name, '|', what)
# canonical_scan forms: patch 2 run on the tree after patch 1 with each form; only candidate.rs differs from R
for name, form in (('sSplit', 'split'), ('sSub', 'subslice'), ('sUnr', 'unrolled'), ('sSubUnr', 'subslice-unrolled'), ('sBool', 'bool'),
                   ('sSplitN', 'split+never'), ('sSubN', 'subslice+never'), ('sUnrN', 'unrolled+never'), ('sSubUnrN', 'subslice-unrolled+never'), ('sBoolN', 'bool+never')):
    tmp = OUT / '.tmp' / name
    subprocess.check_call([sys.executable, '-I', str(HERE / 'TP_rewrite_p2.py'), str(U1), str(tmp), form], stdout=subprocess.DEVNULL)
    emit(name, {C: (tmp / C).read_text()}, 'canonical_scan in form `%s`' % form)
shutil.rmtree(OUT / '.tmp')
# prepared_claim: inlining of the two helpers of the claim-fission text (R has both #[inline(always)])
t = (R / V).read_text()
CFG = '#[cfg(not(feature="future-claim-rows"))]\n'
SUM = CFG + '#[inline(always)]\nfn prepared_claim_sum('; DOT = CFG + '#[inline(always)]\nfn prepared_claim_dot<H:Digest32>('
assert t.count(SUM) == 1 and t.count(DOT) == 1
def attrs(dot, sm):
    a = {'none': '', 'always': '#[inline(always)]\n', 'never': '#[inline(never)]\n'}
    return t.replace(SUM, CFG + a[sm] + 'fn prepared_claim_sum(').replace(DOT, CFG + a[dot] + 'fn prepared_claim_dot<H:Digest32>(')
for name, dot, sm in (('cNN', 'none', 'none'), ('cNevAlw', 'never', 'always'), ('cNevNone', 'never', 'none'), ('cAlwNev', 'always', 'never'), ('cNevNev', 'never', 'never'), ('cNoneAlw', 'none', 'always')):
    emit(name, {V: attrs(dot, sm)}, 'claim fission: prepared_claim_dot inline %s, prepared_claim_sum inline %s' % (dot, sm))
# the floor: prepared_claim as the base tree has it
def text(tree, key): return fx['fns']((tree / V).read_text())[key]['text']
u = t
for k in ('::prepared_claim_sum#1', '::prepared_claim_dot#1', '::prepared_claim#2'):
    cur = text(R, k); assert u.count(cur) == 1, k; u = u.replace(cur + '\n', '')
cur = text(R, '::prepared_claim#1'); assert u.count(cur) == 1
emit('cBase', {V: u.replace(cur, text(BASE, '::prepared_claim#1'))}, 'prepared_claim as in the base tree (one definition, `if cfg!` inside): the floor')
# the fission text with the point loop inside a block of its own
old = '''        for point in 0..6 {
            parts[point+1]=prepared_claim_dot(sem,y1,g,point)?;
        }
        Ok(prepared_claim_sum(k,parts))'''
assert t.count(old) == 1
emit('cBlock', {V: t.replace(old, '''        {
        for point in 0..6 {
            parts[point+1]=prepared_claim_dot(sem,y1,g,point)?;
        }
        }
        Ok(prepared_claim_sum(k,parts))''')}, 'claim fission with the point loop in a block of its own')
for f in (V, C):
    p = OUT / 'B' / f; p.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(R / f, p)
print('B | the reference R: copies of', V, 'and', C)
