#!/usr/bin/env python3
"""Aspis freeze emission: row comparisons. Reads only.
usage:
  fv_frz_emit_compare.py notes  <rows.tsv> <ref-dir>
      every row of the workers' own release-style emissions (ref-<run>.json, made by `fv_frz_emit_run.py rows-ref` with
      the same row rule from the workers' adapted Lean and their Lean logs) against this run: rows present in only one,
      and every row whose outcome differs; a worker row that translated and elaborated and does not now is marked LOST.
  fv_frz_emit_compare.py rename <rows-new.tsv> <rows-old.tsv> <rename_map.tsv>
      the rows of a run on a renamed tree against the rows of the earlier tree, the old names written with the map
      (entries of kind fn/mod/const; a feature entry renames nothing in a function path); rows present in only one,
      and every row whose translates/elaborates/class differ. File names are compared after the same map for files."""
import csv, json, re, sys
from pathlib import Path
def load_tsv(p):
    with open(p) as f: return list(csv.DictReader(f, delimiter='\t'))
def outcome(t, e):
    t = 'yes' if t == 'yes' else 'opaque' if t.startswith('opaque') else 'absent' if t.startswith('not in') else 'no'
    e = 'yes' if e == 'yes' else 'no' if e.startswith('no') else 'not run' if e.startswith('not run') else 'undetermined'
    return t, e
if sys.argv[1] == 'notes':
    rows = load_tsv(sys.argv[2]); ref = Path(sys.argv[3]); diffs = []; tot = {}
    for X in ('v', 'p', 's', 'd', 'c'):
        f = ref / ('ref-%s.json' % X)
        if not f.exists(): continue
        theirs = {r['function']: outcome(r['translates'], r['elaborates']) for r in json.load(open(f))['rows']}
        mine = {r['function']: (outcome(r['translates'], r['elaborates']), r) for r in rows if r['run'] == X}
        n = dict(worker_rows=len(theirs), rows=len(mine), same=0)
        for k, o in theirs.items():
            if k not in mine: diffs.append(dict(run=X, function=k, worker=o, now=None, kind='LOST (row absent now)' if o == ('yes', 'yes') else 'row absent now')); continue
            if mine[k][0] == o: n['same'] += 1; continue
            diffs.append(dict(run=X, function=k, worker=o, now=mine[k][0], kind='LOST' if o == ('yes', 'yes') else 'changed', now_detail=mine[k][1]['translates'][:150] + ' / ' + mine[k][1]['elaborates'][:150]))
        for k in mine:
            if k not in theirs: diffs.append(dict(run=X, function=k, worker=None, now=mine[k][0], kind='new row', now_detail=mine[k][1]['translates'][:100] + ' / ' + mine[k][1]['elaborates'][:100]))
        tot[X] = n
    print(json.dumps(dict(per_run=tot, differences=diffs), indent=1))
elif sys.argv[1] == 'rename':
    new = load_tsv(sys.argv[2]); old = load_tsv(sys.argv[3]); m = load_tsv(sys.argv[4])
    pairs = [(x['old'], x['new']) for x in m if x['kind'].split(' ')[0] in ('fn', 'mod', 'const', 'static', 'type', 'struct') and x['new'] not in ('(deleted)', '')]
    pairs.sort(key=lambda p: -len(p[0]))
    rx = re.compile('(?<![\\w])(' + '|'.join(re.escape(a) for a, _ in pairs) + ')(?=::|$|\\}|<|>|,| |\\))') if pairs else None
    tbl = dict(pairs)
    def ren(s): return rx.sub(lambda mm: tbl[mm.group(1)], s) if rx else s
    fmap = {x['old'].split('file ')[-1]: x['new'] for x in m if x['kind'] == 'file'}
    key = lambda r: (r['run'], r['function'])
    o2 = {}
    for r in old: o2[(r['run'], ren(r['function']))] = r
    n2 = {key(r): r for r in new}
    diffs = []; same = 0
    for k, r in o2.items():
        if k not in n2: diffs.append(dict(kind='row only in the old tree (after the map)', run=k[0], function=k[1], old=[r['translates'], r['elaborates'], r['class']])); continue
        s = n2[k]
        d = [c for c in ('translates', 'elaborates', 'class') if s[c] != r[c]]
        if d: diffs.append(dict(kind='differs: ' + ','.join(d), run=k[0], function=k[1], old=[r[c] for c in d], new=[s[c] for c in d]))
        else: same += 1
    for k, s in n2.items():
        if k not in o2: diffs.append(dict(kind='row only in the new tree', run=k[0], function=k[1], new=[s['translates'], s['elaborates'], s['class']]))
    print(json.dumps(dict(old_rows=len(old), new_rows=len(new), same=same, differences=diffs), indent=1))
