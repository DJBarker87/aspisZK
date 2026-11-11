"""Whole-log axiom audit of W6 compile logs: every '#print axioms' result is parsed
across continuation lines (from 'depends on axioms: [' to the matching ']'); every
axiom name must be propext, Classical.choice or Quot.sound.  Also counts sorryAx
anywhere, "declaration uses 'sorry'", and 'error' lines.
usage: python3 -I PIN2W6_axiom_audit.py <logs_dir> <out.json>"""
import sys, re, json, os
STD = {'propext', 'Classical.choice', 'Quot.sound'}
rows = []; hits = []
for f in sorted(os.listdir(sys.argv[1])):
    if not f.endswith('.log'): continue
    t = open(os.path.join(sys.argv[1], f), errors='replace').read()
    blocks = re.findall(r"depends on axioms: \[(.*?)\]", t, re.S)
    names = {n.strip() for b in blocks for n in b.replace('\n', ' ').split(',') if n.strip()}
    nonstd = sorted(names - STD)
    none = len(re.findall(r'does not depend on any axioms', t))
    r = dict(log=f, axiom_lines=len(blocks) + none, names=sorted(names), nonstandard=nonstd,
             sorryAx=t.count('sorryAx'), sorry_decl=t.count("declaration uses 'sorry'"),
             errors=len(re.findall(r'^\S+:\d+:\d+: error', t, re.M)))
    rows.append(r)
    if nonstd or r['sorryAx'] or r['sorry_decl'] or r['errors']: hits.append(r)
json.dump(dict(logs=len(rows), hits=hits, rows=rows), open(sys.argv[2], 'w'), indent=1)
print('logs audited', len(rows), 'axiom results', sum(r['axiom_lines'] for r in rows), 'hits', len(hits))
for h in hits: print(' ', h['log'], h['nonstandard'], 'sorryAx', h['sorryAx'], 'sorry', h['sorry_decl'], 'errors', h['errors'])
