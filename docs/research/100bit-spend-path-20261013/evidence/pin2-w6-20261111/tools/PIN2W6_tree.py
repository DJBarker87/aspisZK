"""Prepare the PIN2 generator tree (scratch): research lean/J[A-H]* sources and
the fixture evidence dirs' .py/.json files, with every module and data file that
W4/W5 (and earlier W6 families) regenerated for PIN2 substituted under its
original JF name.  A module text is mapped back to its JF name by giving it the
research JF source's import header (the release ports changed imports only).
Writes TREE-SUBSTITUTIONS.json.  usage: python3 -I PIN2W6_tree.py <tree>"""
import sys, os, json, hashlib, subprocess, re
from pathlib import Path
T = Path(sys.argv[1]); W = Path('/Users/dominic/ZK/.worktrees/pin2-lean')
EV = W / 'docs/research/100bit-spend-path-20261013/evidence'; W6 = EV / 'pin2-w6-20261111'
sha = lambda b: hashlib.sha256(b).hexdigest()
def header(t):
    l = t.split('\n'); i = 0
    while i < len(l) and l[i].startswith('import '): i += 1
    return l[:i], '\n'.join(l[i:])
def jfname(rel): return re.sub(r'^(NDO|RPz8|RPt|RPu)_', '', rel)
subs = []
def put_module(rel, text, who):
    jf = jfname(rel); dst = T / 'lean' / f'{jf}.lean'
    if not dst.exists(): subs.append(dict(module=rel, jf=jf, who=who, skipped='no JF original in tree')); return
    oh, _ = header(dst.read_text()); _, body = header(text)
    new = '\n'.join(oh + [body]) if oh else text
    old = dst.read_text(); dst.write_text(new)
    subs.append(dict(module=rel, jf=jf, who=who, before=sha(old.encode()), after=sha(new.encode())))
for who, d in (('W4', EV / 'pin2-w4-20261111/sources'), ('W5', EV / 'pin2-w5-20261111/sources'), ('W6', W6 / 'sources')):
    if d.exists():
        for f in sorted(d.glob('*.lean')): put_module(f.stem, f.read_text(), who)
DATA = {'pin2-w4-20261111/PIN2_JFx_DATA.json': 'evidence/joint-fixture-20261026/JFx_DATA.json',
        'pin2-w4-20261111/PIN2_JFz_SCAN_MANIFEST.json': 'evidence/joint-fixture3-20261026/JFz_SCAN_MANIFEST.json',
        'pin2-w4-20261111/PIN2_JFz_ROWS_MANIFEST.json': 'evidence/joint-fixture3-20261026/JFz_ROWS_MANIFEST.json',
        'pin2-w4-20261111/PIN2_JFw_RECORDS_MANIFEST.json': 'evidence/joint-fixture4-20261026/JFw_RECORDS_MANIFEST.json',
        'pin2-w4-20261111/PIN2_JFp_SHA_INPUT.json': 'evidence/joint-fixture10-20261026/JFp_SHA_INPUT.json'}
for s, d in DATA.items():
    b = (EV / s).read_bytes(); old = (T / d).read_bytes(); (T / d).write_bytes(b)
    subs.append(dict(data=d, source=s, before=sha(old), after=sha(b)))
for root in (EV / 'pin2-w5-20261111/generated', W6 / 'generated'):
    if not root.exists(): continue
    for f in sorted(root.rglob('*')):
        if f.is_file():
            d = T / f.relative_to(root); old = d.read_bytes() if d.exists() else b''
            d.parent.mkdir(parents=True, exist_ok=True); d.write_bytes(f.read_bytes())
            subs.append(dict(data=str(f.relative_to(root)), source=str(f.relative_to(EV)), before=sha(old), after=sha(f.read_bytes())))
json.dump(subs, open(W6 / 'TREE-SUBSTITUTIONS.json', 'w'), indent=1)
print(len(subs), 'substitutions;', sum(1 for s in subs if 'skipped' in s), 'skipped:', [s['module'] for s in subs if 'skipped' in s][:10])
