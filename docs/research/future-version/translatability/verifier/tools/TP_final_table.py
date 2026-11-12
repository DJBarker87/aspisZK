#!/usr/bin/env python3
"""Aspis translatability pass: the per-function table of a release-style emission (final tree). Runs TP_classify.py on
the given scopes, drops its first-pair column (the first tool pair was not run on the final tree) and prints counts.
usage: TP_final_table.py <out.json> <out.md> <status_rows.json> <fntext.json> <verifier raw dir>,<aeneas summary json>,<lean errmap json>
                         <program raw dir>,<aeneas summary json>,<lean errmap json>      (run from the repository root)"""
import json, re, subprocess, sys, collections
from pathlib import Path
OUTJ, OUTM, STATUS, FNTEXT, V, P = sys.argv[1:7]
HERE = Path(__file__).resolve().parent
def normalised(scope):
    """the Lean error map names declarations as the ADAPTED file has them; where the adaptation wrote a module item with
    its full name (`_root_.<namespace>.compact.x`), give it back the emitted name (`compact.x`) so that it matches"""
    raw, summ, errmap = scope.split(',')
    em = json.loads(Path(errmap).read_text())
    for x in em['failing']:
        if x.get('lean'): x['lean'] = re.sub(r'^_root_\.\w+\.', '', x['lean'])
    q = Path(errmap).with_suffix('.normalised.json'); q.write_text(json.dumps(em)); return ','.join((raw, summ, str(q)))
V, P = normalised(V), normalised(P)
subprocess.check_call([sys.executable, '-I', str(HERE / 'TP_classify.py'), OUTJ, OUTM + '.tmp', STATUS, FNTEXT, 'verifier-T2=' + V, 'program-T2=' + P], stdout=subprocess.DEVNULL)
lines = Path(OUTM + '.tmp').read_text().splitlines(); Path(OUTM + '.tmp').unlink()
out = []; counts = collections.Counter()
for i, l in enumerate(lines):
    c = l.split(' | ')
    if len(c) >= 7:
        del c[4]
        if i == 0: c[2], c[3] = 'Translates (second pair, `-abort-on-error` run)', 'Lean against the R1 library'
        elif i > 1:
            tr, le = c[2].strip(), c[3].strip()
            kind = ('does not translate' if tr.startswith('NO') else 'opaque in this emission (named gap)' if tr.startswith('axiom') else
                    'translates and elaborates' if le == 'elaborates' else 'translates, Lean does not elaborate' if le else 'translates, Lean not determined')
            if tr.startswith('axiom') and 'aspis_r1_cost_probe_program' not in l and '`program::' not in c[0]: kind = 'boundary of the program scope (verifier crate item)'
            counts[kind] += 1
    if i == 1: c = ['|---|---|---|---|---|---|']   # the separator row has one column fewer too
    out.append(' | '.join(c))
Path(OUTM).write_text('\n'.join(out) + '\n')
print(json.dumps(dict(rows=len(out) - 2, **counts), indent=1))
