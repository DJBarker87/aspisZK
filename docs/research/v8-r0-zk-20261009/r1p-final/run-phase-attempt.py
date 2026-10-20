#!/usr/bin/env python3
"""One focused env-J attempt, preserving complete launcher evidence."""
import hashlib, json, pathlib, re, subprocess, sys
attempt = int(sys.argv[1]); module = sys.argv[2]
assert 9000 <= attempt <= 9199
root = pathlib.Path(__file__).resolve().parents[1]
src = root / 'lean' / (module + '.lean')
remote = 'dombarker@100.108.41.90'
j = '/home/dombarker/project-offloads/aspis-joint-20261019'
t = '/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
h = '/home/dombarker/project-offloads/r1-privacy-build-integration-20261019'
imports = re.findall(r'^import (\S+)', src.read_text(), re.M)
mathlib = '/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/mathlib/.lake/build/lib/lean'
cmd = ['sha256sum ' + (mathlib if x.startswith('Mathlib.') else j + '/objects') + '/' + x.replace('.', '/') + '.olean' for x in sorted(imports)]
deps = subprocess.check_output(['ssh', remote, 'set -e\n' + '\n'.join(cmd)], text=True)
fp = hashlib.sha256(deps.encode()).hexdigest()[:16]
exists = subprocess.run(['ssh', remote, 'test -e ' + j + '/sources/' + module + '.lean']).returncode == 0
if exists:
    snap = j + '/snapshots/codex-cx-priv-phase-20261021/' + str(attempt)
    subprocess.run(['ssh', remote, 'mkdir -p ' + snap + '; cp ' + j + '/sources/' + module + '.lean ' + snap + '/source.lean; if test -f ' + j + '/objects/' + module + '.olean; then cp ' + j + '/objects/' + module + '.olean ' + snap + '/object.olean; fi'], check=True)
subprocess.run(['scp', str(src), remote + ':' + j + '/sources/' + module + '.lean'], check=True)
p = subprocess.run(['ssh', remote, f'sh {h}/tools/run-joint.sh {attempt} {module} J 7000 7 {fp}'], text=True, capture_output=True)
print(p.stdout, p.stderr, flush=True)
if p.returncode != 0:
    raise SystemExit(p.returncode)
out = subprocess.check_output(['ssh', remote, f'cat {t}/out-{attempt}.log'], text=True)
time = subprocess.check_output(['ssh', remote, f'cat {t}/time-{attempt}.log'], text=True)
def val(pat):
    m = re.search(pat, time)
    return m.group(1) if m else None
r = dict(attempt=attempt, module=module, env='J', source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
         source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
         deps_fingerprint=fp, dependency_objects=deps.splitlines(),
         exit=int(re.search(r'exit=(\d+)', out)[1]), wall=val(r'Elapsed.*: (\S+)'),
         peak_rss_kib=val(r'Maximum resident set size \(kbytes\): (\d+)'), swaps=val(r'Swaps: (\d+)'),
         output=out, timing=time, launcher=p.stdout)
with (root/'r1p-final/phase-attempts-9000-9199.jsonl').open('a') as f: f.write(json.dumps(r)+'\n')
