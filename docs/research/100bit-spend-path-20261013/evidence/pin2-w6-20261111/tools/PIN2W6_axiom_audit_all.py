"""Whole-log axiom audit of the Mac-side PIN2 worker logs (read-only).  Each log is
classified by its compile-table exit code (credited = exit 0); a hit is any
non-standard axiom name, sorryAx, "declaration uses 'sorry'" or error line.
usage: python3 -I PIN2W6_axiom_audit_all.py <out.json>"""
import sys, os, re, json
W = '/Users/dominic/ZK/.worktrees/pin2-lean'; EV = W + '/docs/research/100bit-spend-path-20261013/evidence'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
DIRS = {'W4': ('pin2-w4-20261111', W + '/PIN2-W4-COMPILE.tsv'), 'W5': ('pin2-w5-20261111', W + '/PIN2-W5-COMPILE.tsv'),
        'W3a': ('pin2-w3a-20261111', W + '/PIN2-W3a-COMPILE.tsv'),
        'W3b': ('pin2-w3b-20261111', EV + '/pin2-w3b-20261111/PIN2-W3b-COMPILE.tsv'),
        'W3c': ('pin2-w3c-20261111', W + '/PIN2-W3c-COMPILE.tsv'), 'W6': ('pin2-w6-20261111', EV + '/pin2-w6-20261111/PIN2-W6-COMPILE.tsv')}
out = {}
for k, (d, tsv) in DIRS.items():
    ex = {}
    for l in open(tsv).read().splitlines()[1:]:
        f = l.split('\t')
        if len(f) > 2: ex[f[0]] = f[2]
    L = os.path.join(EV, d, 'logs'); res = dict(logs=0, credited_logs=0, uncredited_logs=0, no_table_row=0, axiom_results=0, credited_hits=[], uncredited_hits=0, uncredited_hit_logs=[])
    for f in sorted(os.listdir(L)):
        if not f.endswith('.log'): continue
        t = open(os.path.join(L, f), errors='replace').read()
        cid = f.split('-', 1)[0]; e = ex.get(cid)
        b = re.findall(r'depends on axioms: \[(.*?)\]', t, re.S)
        names = {n.strip() for x in b for n in x.replace('\n', ' ').split(',') if n.strip()}
        nonstd = sorted(names - STD)
        hit = bool(nonstd or 'sorryAx' in t or "declaration uses 'sorry'" in t or re.search(r'^\S+:\d+:\d+: error', t, re.M))
        res['logs'] += 1; res['axiom_results'] += len(b) + t.count('does not depend on any axioms')
        if e is None: res['no_table_row'] += 1
        if e == '0':
            res['credited_logs'] += 1
            if hit: res['credited_hits'].append(dict(log=f, nonstandard=nonstd, sorryAx=t.count('sorryAx'), sorry_decl=t.count("declaration uses 'sorry'")))
        else:
            res['uncredited_logs'] += 1
            if hit: res['uncredited_hits'] += 1; res['uncredited_hit_logs'].append(f)
    out[k] = res
    print(k, {x: (len(v) if isinstance(v, list) else v) for x, v in res.items()})
json.dump(out, open(sys.argv[1], 'w'), indent=1)
