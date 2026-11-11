"""Find native verifier values hard-coded in the 26 October fixture
generators: every integer literal >= 2^16 in each generator script is looked
up among the limbs of the 26 October native dump (4bb3b3f library, same
inputs), excluding the field modulus and the SHA-256 constants/IV.
usage: python3 -I PIN2W5_hardcoded.py"""
import json, re, subprocess, collections
from pathlib import Path
H = Path(__file__).resolve().parent
D = json.loads((H / 'provenance-26oct/DERIVED-26OCT.json').read_text())
git = lambda *a: subprocess.run(['git', '-C', '/Users/dominic/ZK', *a], capture_output=True, check=True).stdout.decode()
where = collections.defaultdict(set)
for st in ('tx1', 'tx2'):
    for t, v in D[st].items():
        for i, x in v.items():
            for limb in x:
                if limb >= 1 << 16: where[limb].add(f'{st}:tag{t}')
SKIP = {2147483647}
sha_k = set(map(int, re.search(r'def constants : List Nat := \[(.*?)\]', git('show', 'research:lean/JFp_SHA256.lean'), re.S)[1].replace('\n', '').split(',')))
SKIP |= sha_k | {1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}
files = [f for f in git('ls-tree', '-r', '--name-only', 'research', 'evidence/').split('\n')
         if re.match(r'evidence/(joint-fixture|fixture-tx2)[^/]*/[^/]*\.py$', f)]
out = {}
for f in files:
    s = git('show', f'research:{f}')
    hits = collections.Counter()
    for n in map(int, re.findall(r'(?<![\w.])\d{5,10}(?![\w.])', s)):
        if n in SKIP or n not in where: continue
        for w in where[n]: hits[w] += 1
    if hits: out[f] = dict(hits)
(H / 'HARDCODED.json').write_text(json.dumps(out, indent=1, sort_keys=True) + '\n')
print(len(files), 'generator scripts scanned;', len(out), 'contain 26 October native values')
for f, h in sorted(out.items()): print(f, h)
