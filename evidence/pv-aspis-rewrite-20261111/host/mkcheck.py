#!/usr/bin/env python3
"""pv-aspis-rewrite-20261111, gate D: focused Lean check file for the rewritten functions of one emission.
Adapted from pv-combined-20261111 tools/t2check.py (parts 2 and 4); the splice library splice2.py is imported from
that job, read only. For the named target functions of emit/TAG/generated (tool k2) and package g2:
 * every target is carried from the emission (also when the package already defines that name: its text changed);
 * a function a carried block refers to is taken from the package when the package defines it with a real body, and
   carried from the emission otherwise (when the emission has a real body for it);
 * an opaque item of the emission that the package does not declare becomes an axiom of the check file;
 * the carried text is machine-emitted text copied verbatim except that the doc comment and the attribute line are
   dropped, inside `namespace ProverPin2.RW`, so that it elaborates against the package's types as they stand.
No body is written or edited here. Placeholder bodies and missing items are reported and make the result 'incomplete'.
usage: mkcheck.py TAG TARGET_LEAN_NAME..."""
import sys, re, json, pathlib, hashlib
W = pathlib.Path('/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111')
C = pathlib.Path('/home/dombarker/project-offloads/codex-pv-combined-20261111')
sys.path.insert(0, str(C / 'tools'))
from splice2 import blocks, Pkg, Emission, tokens, resolve, rust_path, source_span, PH, sha
import os
tag = sys.argv[1]; TARGETS = sys.argv[2:]
# PV_KEEP_AXIOMS=1: a function that is not a target and is an opaque item (axiom) of the package stays the package's
# axiom; its emitted body and what only that body needs are not carried.
KEEP_AXIOMS = os.environ.get('PV_KEEP_AXIOMS') == '1'
EM = W / 'emit' / tag / 'generated'; G2 = C / 'pkg/g2'; O = W / 'check' / tag; O.mkdir(parents=True, exist_ok=True)
base = {n: (G2 / 'ProverPin2' / n).read_text() for n in ['Types.lean', 'TypesExternal.lean', 'FunsExternal.lean', 'Funs.lean']}
pkg = Pkg(base['Funs.lean'], base['FunsExternal.lean'], base['Types.lean'], base['TypesExternal.lean']); em = Emission(EM)
carry = {}; new_ax = {}; types_used = set(); kept = []; notes = []; bad = []
work = [(t, True) for t in TARGETS]
while work:
    n, forced = work.pop()
    if n in carry: continue
    if n not in em.f:
        (bad if forced else notes).append(f'{n}: not in the emission'); continue
    eb = em.fb[em.f[n][0]]; st = pkg.status(n)
    if st == 'defined' and not forced:
        pb = pkg.fb[pkg.f[n][0]]; kept.append(dict(name=n, package_text_identical_to_emission=pb['text'].strip() == eb['text'].strip())); continue
    if st == 'axiom' and not forced and KEEP_AXIOMS:
        kept.append(dict(name=n, package_axiom_used_in_place_of_the_emitted_body=True)); continue
    if PH.search(eb['body']):
        (bad if forced else notes).append(f'{n}: placeholder body in the emission (package status {st})'); continue
    carry[n] = em.f[n][0]
    for t in tokens(eb['body']):
        where, c = resolve(t, ('ef', em.f), ('ex', em.x), ('et', em.t), ('pf', pkg.f), ('px', pkg.x), ('pt', pkg.t))
        if where == 'ef' and c != n: work.append((c, False))
        elif where == 'ex' and c not in pkg.x and c not in pkg.f: new_ax[c] = em.x[c]
        elif where == 'et': types_used.add(c)
for b in new_ax.values():
    for t in tokens(b['body']):
        where, c = resolve(t, ('et', em.t), ('pt', pkg.t))
        if where == 'et': types_used.add(c)
# types of the emission that the package does not declare (new Rust types) are carried too, with the emission's
# types they mention, in the order of the emission
tw = [c for c in types_used if c not in pkg.t]; new_types = set()
while tw:
    x = tw.pop()
    if x in new_types: continue
    new_types.add(x)
    for t in tokens(em.t[x]['body']):
        w2, c2 = resolve(t, ('et', em.t), ('pt', pkg.t))
        if w2 == 'et' and c2 != x and c2 not in pkg.t: tw.append(c2)
type_order = [b['name'] for b in em.tb if b['name'] in new_types]
tdiff = []
for c in sorted(types_used):
    if c not in pkg.t: tdiff.append(dict(type=c, kind='declared by the emission, absent from the package; carried'))
    elif pkg.t[c]['text'].strip() != em.t[c]['text'].strip(): tdiff.append(dict(type=c, kind='text differs'))
def strip_head(b):
    t = b['text']; body = t[t.find('-/') + 2:] if '-/' in t else t
    return re.sub(r'\A\s*@\[.*?\]\s*\n', '\n', body, count=1, flags=re.S).strip('\n')
L = ['import ProverPin2.Funs', 'open Aeneas Aeneas.Std Result ControlFlow Error', 'set_option linter.unusedVariables false', 'set_option maxHeartbeats 1000000', 'set_option maxRecDepth 2048', '',
     'namespace ProverPin2', 'namespace RW', 'noncomputable section', '']
for c in type_order:
    L += [f'-- type of the emission that package g2 does not declare, block sha256 {sha(em.t[c]["text"])}', strip_head(em.t[c]), '']
for n, b in sorted(new_ax.items()):
    L += [f'-- opaque item of the emission that package g2 does not declare, block sha256 {sha(b["text"])}', strip_head(b), '']
for n, i in sorted(carry.items(), key=lambda x: x[1]):
    L += [f'-- block emitted by tool k2 (7271db7e), sha256 {sha(em.fb[i]["text"])}, source {source_span(em.fb[i]["doc"])}', strip_head(em.fb[i]), '']
L += ['end', 'end RW', 'end ProverPin2', '']
sig = []
for n in TARGETS:
    if n in carry:
        st = pkg.status(n)
        if st == 'axiom': L.append(f'example : type_of% @ProverPin2.RW.{n} = type_of% @{n} := rfl'); sig.append(n)
        elif st in ('placeholder', 'defined'): L.append(f'example : type_of% @ProverPin2.RW.{n} = type_of% @ProverPin2.{n} := rfl'); sig.append(n)
        L += [f'#check @ProverPin2.RW.{n}', f'#print axioms ProverPin2.RW.{n}']
L.append(f'-- {len(carry)} carried blocks, {len(new_ax)} new opaque items, {len(sig)} signature checks')
(O / 'RwCheck.lean').write_text('\n'.join(L) + '\n')
res = dict(tag=tag, targets=TARGETS, emission=str(EM), funs_sha256=hashlib.sha256((EM / 'Funs.lean').read_bytes()).hexdigest() if (EM / 'Funs.lean').exists() else None,
           carried_blocks=[dict(name=n, sha256=sha(em.fb[i]['text']), bytes=len(em.fb[i]['text'].encode()), source=source_span(em.fb[i]['doc']), package_status=pkg.status(n), target=n in TARGETS) for n, i in sorted(carry.items(), key=lambda x: x[1])],
           package_definitions_used_not_carried=kept, new_opaque_items=[dict(name=n, rust_path=rust_path(b['doc']), sha256=sha(b['text'])) for n, b in sorted(new_ax.items())],
           type_differences=tdiff, notes=notes, target_failures=bad, complete=not bad,
           check_file=dict(path=str(O / 'RwCheck.lean'), sha256=hashlib.sha256((O / 'RwCheck.lean').read_bytes()).hexdigest(), signature_checks=sig))
(O / 'mkcheck.json').write_text(json.dumps(res, indent=1) + '\n')
print(json.dumps(dict(tag=tag, carried=[(b['name'], b['package_status']) for b in res['carried_blocks']], kept=len(kept), new_opaque=[b['name'] for b in res['new_opaque_items']], type_differences=tdiff, notes=notes, target_failures=bad), indent=1))
