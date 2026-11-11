"""Scan the release sources of the non-fixture modules downstream of the
fixture data for 26 October values: integer literals >= 2^16 that are limbs of
the 26 October native dump (not modulus / SHA constants), the 26 October seed or
public-length constants (1455, 1530) and the 26 October query list values.
usage: python3 -I PIN2W6_nonjf_scan.py <scan_dir> <out.json>"""
import sys, os, re, json, collections, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
out = sys.argv[2]; sys.argv = sys.argv[:2]
import PIN2W6_ready as R, PIN2W6_src as S
D = json.load(open(S.EV / 'pin2-w5-20261111/provenance-26oct/DERIVED-26OCT.json'))
where = collections.defaultdict(set)
for st in ('tx1', 'tx2'):
    for t, v in D[st].items():
        for i, x in v.items():
            for limb in x:
                if limb >= 1 << 16: where[limb].add(f'{st}:tag{t}')
SKIP = {2147483647, 2147483648, 4294967295, 4294967296}
idx = collections.defaultdict(set)
for l in open(R.scan + '/../w6/research-lean.tsv' if False else '/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w6/research-lean.tsv'):
    b, p = l.rstrip('\n').split('\t'); idx[p.rsplit('/', 1)[-1][:-5]].add((b, p))
git = lambda *a: subprocess.run(['git', '-C', str(S.W), *a], capture_output=True).stdout
rows = {}
for m in sorted(x for x in R.dep if not R.FIX.match(x)):
    b, note = S.release(m)
    if b is None:
        c = idx.get(m, set())
        if len({x for x, _ in c}) == 1: p = sorted(c)[0][1]; b = git('show', f'research:{p}'); note = f'unique blob research:{p}'
        else: rows[m] = dict(source=None, candidates=len({x for x, _ in c})); continue
    s = re.sub(r'--.*', '', b.decode())
    nat = sorted({int(n) for n in re.findall(r'(?<![\w.])\d{5,}(?![\w.])', s) if int(n) in where and int(n) not in SKIP})
    lens = sorted(set(re.findall(r'(?<![\w.])(1455|1530)(?![\w.])', s)))
    if nat or lens: rows[m] = dict(source=note, native=nat[:12], n_native=len(nat), lengths=lens)
nos = [m for m, r in rows.items() if r.get('source') is None]
hit = {m: r for m, r in rows.items() if r.get('source')}
print('non-fixture dep', sum(1 for x in R.dep if not R.FIX.match(x)), 'with native/length literals', len(hit), 'no unique source', len(nos))
for m, r in sorted(hit.items()): print(' ', m, r['n_native'], r['lengths'], r['native'][:4])
json.dump(dict(hits=hit, no_source=nos), open(out, 'w'), indent=1)
