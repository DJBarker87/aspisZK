#!/usr/bin/env python3
"""Aspis translatability pass: variant trees for attributing compute to single rewrites. Each variant is the batch tree
with ONE rewrite put back to an earlier text; the difference in replay compute between the batch and the variant is
what that rewrite costs in the batch's context (costs are not additive: the compiler's choices depend on the rest).
usage: TP_variants.py <restored tree (base + patch 0)> <batch tree> <base tree> <out dir>
writes <out dir>/<name>/ with the full files that differ from the batch tree, and prints one line per variant."""
import re, sys, shutil
from pathlib import Path
T0, TB, BASE, OUT = [Path(x) for x in sys.argv[1:5]]
src_fx = Path(__file__).with_name('TP_fntext.py').read_text().split("rep = {}")[0].replace("A, B, OUT = sys.argv[1:4]; FILES = sys.argv[4:]", "")
fx = {}; exec(compile(src_fx, 'TP_fntext_head', 'exec'), fx)
V = 'crates/aspis-r1-cost-probe/src/verifier.rs'; C = 'crates/aspis-r1-cost-probe/src/candidate.rs'; S = 'crates/aspis-r1-cost-probe/src/r1_semantic.rs'
def text(tree, f, key): return fx['fns']((tree / f).read_text())[key]['text']
def swap(f, key, other_tree, other_key=None):
    t = (TB / f).read_text(); cur = text(TB, f, key); new = text(other_tree, f, other_key or key)
    assert t.count(cur) == 1, (f, key); assert cur != new, (f, key, 'no difference')
    return t.replace(cur, new)
def emit(name, files, what):
    for f, t in files.items():
        p = OUT / name / f; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(t)
    print(name, '|', what, '|', ', '.join(files))
# C: claims as pinned
emit('vC', {S: swap(S, '::claims#1', T0)}, 'claims put back to the pinned raw-pointer form')
# D: prepared_claim as in the base tree (one definition with `if cfg!`), helpers and the second definition removed
t = (TB / V).read_text()
for k in ('::prepared_claim_sum#1', '::prepared_claim_dot#1', '::prepared_claim#2'):
    cur = text(TB, V, k); assert t.count(cur) == 1, k; t = t.replace(cur + '\n', '')
cur = text(TB, V, '::prepared_claim#1'); assert t.count(cur) == 1
t = t.replace(cur, text(BASE, V, '::prepared_claim#1'))
emit('vD', {V: t}, 'prepared_claim put back to the base tree text (one definition, `if cfg!` inside)')
# E: Prepared::new as pinned (the helper second_alpha stays, unused)
emit('vE', {V: swap(V, 'impl Prepared::new#1', T0)}, 'Prepared::new put back to the pinned text')
# F: for_range as pinned
emit('vF', {V: swap(V, 'impl QueryGeometry::for_range#1', T0)}, 'QueryGeometry::for_range put back to the pinned text')
# G: canonical_scan as pinned
emit('vG', {C: swap(C, '::canonical_scan#1', T0)}, 'canonical_scan put back to the pinned text')
# H: the program crate as in the restored tree
files = {}
for p in sorted((T0 / 'programs/r1-cost-probe').rglob('*')):
    if p.is_file():
        rel = str(p.relative_to(T0)); q = TB / rel
        if not q.exists() or q.read_bytes() != p.read_bytes(): files[rel] = p.read_text()
emit('vH', files, 'the program crate put back to the restored tree (adapter rewrites and the unobserved call out)')
# I, J, K: inlining choices for the two functions that sit inside Prepared::new
def attr(t, old, new):
    assert t.count(old) == 1, old[:60]; return t.replace(old, new)
PC = '#[cfg(not(feature="future-claim-rows"))]\nfn prepared_claim<H:Digest32>('
SA = '#[inline(always)]\nfn second_alpha<H:Digest32>('
t = (TB / V).read_text()
emit('vI', {V: attr(t, PC, '#[cfg(not(feature="future-claim-rows"))]\n#[inline(never)]\nfn prepared_claim<H:Digest32>(')}, 'prepared_claim (fission text) not inlined into Prepared::new')
emit('vJ', {V: attr(t, SA, '#[inline(never)]\nfn second_alpha<H:Digest32>(')}, 'second_alpha not inlined into Prepared::new')
emit('vK', {V: attr(attr(t, PC, '#[cfg(not(feature="future-claim-rows"))]\n#[inline(never)]\nfn prepared_claim<H:Digest32>('), SA, '#[inline(never)]\nfn second_alpha<H:Digest32>(')}, 'both not inlined')
# T0: the restored tree itself (control: must reproduce the restoration gate's compute);
# P: the restored tree with prepared_claim left as the base tree has it (is the restoration then compute-neutral?)
files = {}
for root in ('crates/aspis-r1-cost-probe', 'programs/r1-cost-probe'):
    for p in sorted((T0 / root).rglob('*')):
        if p.is_file():
            rel = str(p.relative_to(T0)); q = TB / rel
            if not q.exists() or q.read_bytes() != p.read_bytes(): files[rel] = p.read_text()
emit('vT0', files, 'every batch file put back: the restored tree (control)')
t = files[V]; cur = text(T0, V, '::prepared_claim#1'); cur2 = text(T0, V, '::prepared_claim#2')
assert t.count(cur) == 1 and t.count(cur2) == 1
t = t.replace(cur2 + '\n', '').replace(cur, text(BASE, V, '::prepared_claim#1'))
emit('vP', dict(files, **{V: t}), 'the restored tree with prepared_claim as in the base tree (one definition, `if cfg!` inside)')
# B: the batch tree's own copy of every file any variant touches (laid down before each variant)
allf = set()
for d in OUT.iterdir():
    if d.is_dir() and d.name != 'B':
        for p in d.rglob('*'):
            if p.is_file(): allf.add(str(p.relative_to(d)))
for f in sorted(allf):
    p = OUT / 'B' / f; p.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(TB / f, p)
print('B | the batch tree copies of', len(allf), 'files')
