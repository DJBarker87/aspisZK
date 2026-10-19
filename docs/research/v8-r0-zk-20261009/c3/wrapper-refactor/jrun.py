#!/usr/bin/env python3
"""jrun.py ATTEMPT MODULE MANIFEST -- one env-J compile through run-joint.sh (no extra lock).
Deps fingerprint as joint-drive.py: sha256 over sorted project imports (manifest imports for a manifest
module; for a new module every import with a J object) and their J object sha256s, first 16 hex.
Appends the record to ./evidence-j.jsonl and, for manifest modules, to J/evidence/attempts.jsonl
(same format as joint-drive.py, plus "by") so the driver sees the rebuild."""
import sys, os, re, json, hashlib, subprocess, datetime
from zoneinfo import ZoneInfo
T = '/home/dombarker/project-offloads/aspis-fs-generic-20261006'
H = '/home/dombarker/project-offloads/r1-privacy-build-integration-20261019'
J = '/home/dombarker/project-offloads/aspis-joint-20261019'
A, m, mf = int(sys.argv[1]), sys.argv[2], sys.argv[3]
assert 5600 <= A <= 5649 or 5700 <= A <= 5749, 'attempt outside assigned 5600-5649/5700-5749'
man = json.load(open(mf)); mods = {e['module']: e for e in man['order']}
src = f'{J}/sources/{m.replace(".", "/")}.lean'
sha = hashlib.sha256(open(src, 'rb').read()).hexdigest()
# guard (lead, 2026-10-19): J source must equal the sha I expect; no newer source of this module from another worker
exp = dict(l.split() for l in open('expected-sha.txt')) if os.path.exists('expected-sha.txt') else {}
if m in exp and exp[m] != sha: sys.exit(f'STOP: J source of {m} is {sha[:16]}, expected {exp[m][:16]} (changed by someone else?)')
for l in open(f'{H}/evidence/sent.txt'):
    f = l.split()
    if len(f) >= 4 and f[3] == m.replace('.', '/') and f[0] != sha and int(f[2]) >= 5532 and not (5600 <= int(f[2]) <= 5649 or 5700 <= int(f[2]) <= 5749):
        sys.exit(f'STOP: other worker sent a different source of {m}: {l.strip()}')
IMP = re.compile(r'^\s*import\s+([\w.]+)')
imps = [mm.group(1) for l in open(src) for mm in [IMP.match(l)] if mm]
def objp(x): return f'{J}/objects/{x.replace(".", "/")}.olean'
def objsha(x): return hashlib.sha256(open(objp(x), 'rb').read()).hexdigest() if os.path.exists(objp(x)) else 'missing'
if m in mods:
    if mods[m]['sha256'] != sha: print('WARNING: J source differs from manifest sha')
    deps = sorted(x for x in mods[m]['imports'] if x in mods)
else:
    # new (non-manifest) module: TRANSITIVE project closure, so a changed indirect dependency
    # (e.g. the re-extracted CertBuildExtracted under an unchanged direct import) is a new input
    def pimps(x):
        f = f'{J}/sources/{x.replace(".", "/")}.lean'
        return [mm.group(1) for l in open(f) for mm in [IMP.match(l)] if mm] if os.path.exists(f) else []
    seen, st = set(), [x for x in imps]
    while st:
        x = st.pop()
        if x in seen or x.startswith(('Mathlib', 'Aeneas', 'Lean', 'Std', 'Init')) or not os.path.exists(objp(x)): continue
        seen.add(x); st.extend(pimps(x))
    deps = sorted(seen)
fp = hashlib.sha256(';'.join(f'{x}={objsha(x)}' for x in deps).encode()).hexdigest()[:16]
now = datetime.datetime.now(ZoneInfo('Europe/London'))
ps = subprocess.run("ps -eo pid,rss,etime,cmd | grep -E 'bin/lean|aeneas|charon|cargo' | grep -v grep",
                    shell=True, capture_output=True, text=True).stdout.strip()
gate = {'london': now.strftime('%Y-%m-%d %H:%M:%S'), 'other_jobs': ps}
p = subprocess.run(['sh', f'{H}/tools/run-joint.sh', str(A), m.replace('.', '/'), 'J', '7000', '7', fp],
                   capture_output=True, text=True)
out = open(f'{T}/evidence/out-{A}.log').read() if os.path.exists(f'{T}/evidence/out-{A}.log') else p.stdout
tl = open(f'{T}/evidence/time-{A}.log').read() if os.path.exists(f'{T}/evidence/time-{A}.log') else ''
def tv(pat):
    mm = re.search(pat, tl); return mm.group(1).strip() if mm else None
ex = re.search(r'exit=(\d+)', out)
r = {'attempt': A, 'module': m, 'kind': mods[m]['kind'] if m in mods else 'new-r1p-checker-wrapper',
     'repo_source': mods[m]['source'] if m in mods else f'docs/research/v8-r0-zk-20261009/lean/{m.replace(".", "/")}.lean',
     'source_sha256': sha, 'deps_fingerprint': fp, 'deps': deps, 'gate': gate, 'gate_waits': 0,
     'launcher_stdout_head': p.stdout.splitlines()[:3],
     'exit': int(ex.group(1)) if ex else p.returncode,
     'wall': tv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),
     'peak_rss_kib': int(tv(r'Maximum resident set size \(kbytes\): (\d+)') or 0),
     'swaps': int(tv(r'Swaps: (\d+)') or 0),
     'axioms': [' '.join(x.split()) for x in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))", out, re.M | re.S)],
     'errors': [l for l in out.splitlines() if 'error' in l][:8],
     'by': 'codex/r1p-checker-wrapper-20261019 (jrun.py)'}
open('evidence-j.jsonl', 'a').write(json.dumps(r) + '\n')
if m in mods and ex: open(f'{J}/evidence/attempts.jsonl', 'a').write(json.dumps(r) + '\n')
print(A, m, 'exit', r['exit'], r['wall'], r['peak_rss_kib'], 'swaps', r['swaps'])
print('\n'.join(p.stdout.splitlines()[:3]))
for a in r['axioms']: print('  ', a)
for e in r['errors']: print('  ERR', e)
