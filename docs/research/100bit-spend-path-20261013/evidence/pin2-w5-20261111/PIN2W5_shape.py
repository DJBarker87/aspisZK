"""Shape audit: (1) generator windows vs native windows; (2) for every
regenerated source, the release text and the PIN2 text with every numeral
replaced by '#' must be identical (only literals move), else list the lines.
usage: python3 -I PIN2W5_shape.py"""
import json, re, subprocess, sys
from pathlib import Path
H = Path(__file__).resolve().parent
D = json.loads((H / 'PIN2W5_VALUES.json').read_text())
W = json.loads((H / 'generated/evidence/joint-fixture11-20261026/JFm_WINDOWS.json').read_text())
P = 2147483647; res = {}
res['windows_equal_native'] = len(W) == 27 and all(all(w[k] == r[k] for k in ('frame', 'before', 'absorbed', 'read', 'after')) for w, r in zip(W, D['semantic_rows']))
res['coordinates_equal_tag0'] = all(W[i]['coordinates'] == D['tx1']['0'][str(i)][:4] for i in range(25))
pw = json.loads((H / 'generated/evidence/fixture-tx2g-20261026/JFw_POWERS.json').read_text())
res['powers1_equal_gamma'] = pw[1] == D['tx1']['4']['27']
pv = json.loads((H / 'generated/evidence/fixture-tx2e-20261026/JFs_TX2_POINT_VALUES.json').read_text())
res['geo_queries_equal_tag5'] = sorted({(r['row'], r['index']) for r in pv['records'] if r['kind'] == 0}) == [(10 + i, D['tx1']['5'][str(10 + i)][0]) for i in range(12)]
norm = lambda s: re.sub(r'\d+', '#', s)
shape = {}
for f in sorted((H / 'sources').glob('*.lean')):
    try: rel = subprocess.run(['git', '-C', '/Users/dominic/ZK', 'show', f'research:lean/{f.name}'], capture_output=True, check=True).stdout.decode()
    except subprocess.CalledProcessError: shape[f.stem] = 'new module (no release source)'; continue
    a, b = norm(rel).split('\n'), norm(f.read_text()).split('\n')
    if a != b:
        diff = [(i, x, y) for i, (x, y) in enumerate(zip(a, b)) if x != y][:6]
        shape[f.stem] = dict(release_lines=len(a), pin2_lines=len(b), first_differences=diff)
res['shape_changes'] = shape
print(json.dumps({k: (v if k != 'shape_changes' else {m: (s if isinstance(s, str) else {'release_lines': s['release_lines'], 'pin2_lines': s['pin2_lines'], 'n': len(s['first_differences'])}) for m, s in v.items()}) for k, v in res.items()}, indent=1))
(H / 'SHAPE.json').write_text(json.dumps(res, indent=1) + '\n')
