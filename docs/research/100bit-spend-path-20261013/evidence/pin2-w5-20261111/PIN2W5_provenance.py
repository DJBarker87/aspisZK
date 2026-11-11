"""Provenance check: the 26 October fixture's transcript-dependent literals
against a native dump of the 26 October inputs made with the frozen 4bb3b3f
library (same dumper source).  Reads only research blobs (git show).
usage: python3 -I PIN2W5_provenance.py <DERIVED-26OCT.json> <out.json>"""
import json, re, subprocess, sys
from pathlib import Path
git = lambda p: subprocess.run(['git', '-C', '/Users/dominic/ZK', 'show', f'research:{p}'], capture_output=True, check=True).stdout.decode()
D = json.loads(Path(sys.argv[1]).read_text()); res = []
def check(name, ok, detail=''):
    res.append(dict(item=name, equal=bool(ok), detail=detail)); print(('EQUAL ' if ok else 'DIFF  ') + name, detail)
# 1. JFm_WINDOWS.json (row windows: frame, before, absorbed, read, after)
W = json.loads(git('evidence/joint-fixture11-20261026/JFm_WINDOWS.json'))
for k in ('frame', 'before', 'absorbed', 'read', 'after'):
    check(f'JFm_WINDOWS.{k} (27 rows) = semantic transcript SHA calls', all(w[k] == r[k] for w, r in zip(W, D['semantic_rows'])) and len(W) == len(D['semantic_rows']) == 27)
# coordinates in JFm_WINDOWS = tag 0 values (challenges then alphas) for rows 0..24
t0 = D['tx1']['0']; t3 = D['tx1']['3']
check('JFm_WINDOWS.coordinates rows 0..24 = trace tag 0 (challenges.with_alphas), c0 limbs', all(W[i]['coordinates'] == t0[str(i)][:4] for i in range(25)))
# 2. JFm_Coordinates value00..24
src = git('lean/NDO_JFm_Coordinates.lean')
vals = [list(map(int, re.findall(r'(\d+)#u32', m))) for m in re.findall(r'def value\d\d : aspis_core.field.QM31 := (.*)', src)]
check('NDO_JFm_Coordinates.value00..24 = trace tag 0 indices 0..24', len(vals) == 25 and all(vals[i] == t0[str(i)][:4] for i in range(25)))
# 3. JFr_coefficients.json running/boundary/value/alpha = tag 1 (round checks) and tag 0 alphas
C = json.loads(git('evidence/joint-fixture9-20261026/JFr_coefficients.json')); t1 = D['tx1']['1']
check('JFr_coefficients running/boundary/value = trace tag 1 (3*round+j)', all([c['running'], c['boundary'], c['value']] == [t1[str(3*c['round']+j)][:4] for j in range(3)] for c in C))
check('JFr_coefficients alpha = trace tag 0 index 15+round', all(c['alpha'] == t0[str(15 + c['round'])][:4] for c in C))
# 4. gamma hard-coded in JFw_generate.py = trace tag 4 index 27 (Transcript::scalar row 27)
G = list(map(int, re.search(r'G=\[(.*?)\]', git('evidence/fixture-tx2g-20261026/JFw_generate.py'))[1].split(',')))
check('JFw_generate.py G (gamma) = trace tag 4 index 27', G == D['tx1']['4']['27'])
# 5. JFw_NUMERIC_PREFLIGHT dots = tx2 tag 9 (query 10, four dots); circle/selected = tx2 tag 10 index 20
N = json.loads(git('evidence/fixture-tx2g-20261026/JFw_NUMERIC_PREFLIGHT.json')); t9 = D['tx2']['9']; t10 = D['tx2']['10']
check('JFw_NUMERIC_PREFLIGHT.dots = tx2 tag 9 indices 40..43 (query 10)', N['dots'] == [t9[str(40 + s)] for s in range(4)])
check('JFw_NUMERIC_PREFLIGHT.circle = tx2 tag 10 index 20 (circle fold, query 10)', N['circle'] == t10['20'])
check('JFw_NUMERIC_PREFLIGHT.selected = circle', N['selected'] == N['circle'])
# 6. checkpoint fields (stage 1 output) = tags 4/5/11/12
ck = bytes.fromhex(D['results']['tx1_checkpoint']); le = lambda b: [int.from_bytes(b[i:i+4], 'little') for i in range(0, len(b), 4)]
check('checkpoint gamma [176,208) = tag 4 index 27', le(ck[176:208]) == D['tx1']['4']['27'])
check('checkpoint state [80,112) = final opening transcript state', list(ck[80:112]) == D['opening_transcript']['final_state'])
qs = [int.from_bytes(ck[320+4*i:324+4*i], 'little') for i in range(22)]
check('checkpoint queries [320,408) = tag 5 indices 0..21', qs == [D['tx1']['5'][str(i)][0] for i in range(22)])
check('checkpoint semantic alphas [408,568) = tag 0 indices 15..24', [le(ck[408+16*i:424+16*i]) for i in range(10)] == [D['tx1']['0'][str(15+i)][:4] for i in range(10)])
check('checkpoint z [568,632) = tag 3 indices 0..3', [le(ck[568+16*i:584+16*i]) for i in range(4)] == [D['tx1']['3'][str(i)][:4] for i in range(4)])
check('checkpoint claim [632,664) = tag 14 index 7', le(ck[632:664]) == D['tx1']['14']['7'])
check('checkpoint rhs [664,696) = tag 11 index 9', le(ck[664:696]) == D['tx1']['11']['9'])
Path(sys.argv[2]).write_text(json.dumps(res, indent=1) + '\n')
