"""Source resolution for a module compiled into overlay-PIN2-W4.
Order: W6 sources/ (this job's regenerated or restated text) > the exact source
text last compiled with exit 0 into overlay-PIN2-W4 by W4/W5 (matched by the
sha256 recorded in PIN2-W4/W5-COMPILE.tsv) > the unchanged release source on
research (lean/, evidence/replay-dry9-20261027/, replay-tops1/2-20261027/; each
of these names has exactly one blob on research, checked by PIN2W6_classify)."""
import hashlib, subprocess
from pathlib import Path
W = Path('/Users/dominic/ZK/.worktrees/pin2-lean')
EV = W / 'docs/research/100bit-spend-path-20261013/evidence'
W6 = EV / 'pin2-w6-20261111'
git = lambda *a: subprocess.run(['git', '-C', str(W), *a], capture_output=True)
last = {}
for t in ('PIN2-W4-COMPILE.tsv', 'PIN2-W5-COMPILE.tsv'):
    for l in (W / t).read_text().splitlines()[1:]:
        f = l.split('\t')
        if f[2] == '0': last[f[1]] = (f[5], t[:7])
sha = lambda b: hashlib.sha256(b).hexdigest()
def release(m):
    for p in (f'lean/{m}.lean', f'evidence/replay-dry9-20261027/{m}.lean',
              f'evidence/replay-tops1-20261027/{m}.lean', f'evidence/replay-tops2-20261027/{m}.lean'):
        r = git('show', f'research:{p}')
        if r.returncode == 0:
            blob = git('rev-parse', f'research:{p}').stdout.decode()[:12]
            return r.stdout, f'release source UNCHANGED research:{p} blob {blob}'
    return None, None
def source(m, prefer_w6=True):
    f = W6 / 'sources' / f'{m}.lean'
    if prefer_w6 and f.exists(): return f.read_bytes(), 'W6 source sources/' + f.name
    if m in last:
        want, who = last[m]
        for d in ('pin2-w5-20261111/sources', 'pin2-w4-20261111/sources'):
            g = EV / d / f'{m}.lean'
            if g.exists() and sha(g.read_bytes()) == want: return g.read_bytes(), f'same source as {who} ({d}, sha {want[:12]})'
        b, n = release(m)
        if b is not None and sha(b) == want: return b, f'same source as {who} ({n})'
        raise SystemExit(f'{m}: no source with the recorded sha {want}')
    return release(m)
