#!/usr/bin/env python3
"""One focused env-J attempt, preserving complete launcher evidence."""
import hashlib, json, pathlib, re, subprocess, sys
attempt = int(sys.argv[1]); module = sys.argv[2]
assert 8500 <= attempt <= 8599
root = pathlib.Path(__file__).resolve().parents[1]
src = root / 'lean' / (module + '.lean')
if not src.exists():
    spend = root.parent / '100bit-spend-path-20261013/lean'
    src = spend / (module + '.lean')
    if not src.exists() and module.startswith('R1'):
        src = spend / (module[2:] + '.lean')
assert src.is_file(), src
source_digest = hashlib.sha256(src.read_bytes()).hexdigest()
remote = 'dombarker@100.108.41.90'
j = '/home/dombarker/project-offloads/aspis-joint-20261019'
t = '/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
h = '/home/dombarker/project-offloads/r1-privacy-build-integration-20261019'
subprocess.run(['ssh', remote, f'test ! -e {t}/out-{attempt}.log && test ! -e {t}/sha-{attempt}.txt && test ! -e {t}/time-{attempt}.log'], check=True)
imports = re.findall(r'^import (\S+)', src.read_text(), re.M)
lookup = """import pathlib, json, subprocess
j = pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019/objects')
e = json.loads(pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths = [j] + [pathlib.Path(p) for p in e['LEAN_PATH'].split(':')]
for m in IMPORTS:
    found = next((p / (m.replace('.', '/') + '.olean') for p in paths if (p / (m.replace('.', '/') + '.olean')).exists()), None)
    if found is None: raise SystemExit('missing dependency object: ' + m)
    print(subprocess.check_output(['sha256sum', str(found)], text=True).strip())
""".replace('IMPORTS', repr(sorted(imports)))
import shlex
deps = subprocess.check_output(['ssh', remote, 'python3 -c ' + shlex.quote(lookup)], text=True)
fp = hashlib.sha256(deps.encode()).hexdigest()[:16]
exists = subprocess.run(['ssh', remote, 'test -e ' + j + '/sources/' + module + '.lean']).returncode == 0
if exists:
    assert module in ['R1Z/SerJoinOrderObstruction'], 'only this workers new module may be revised'
    snap = j + '/snapshots/codex-cx-ser-join-20261021/' + str(attempt)
    subprocess.run(['ssh', remote, 'mkdir -p ' + snap + '; cp ' + j + '/sources/' + module + '.lean ' + snap + '/source.lean; if test -f ' + j + '/objects/' + module + '.olean; then cp ' + j + '/objects/' + module + '.olean ' + snap + '/object.olean; fi'], check=True)
subprocess.run(['scp', str(src), remote + ':' + j + '/sources/' + module + '.lean'], check=True)
p = subprocess.run(['ssh', '-o', 'ServerAliveInterval=30', '-o', 'ServerAliveCountMax=3', remote, f'sh {h}/tools/run-joint.sh {attempt} {module} J 7000 7 {fp}'], text=True, capture_output=True, timeout=1200)
print(p.stdout, p.stderr, flush=True)
if p.returncode != 0:
    raise SystemExit(p.returncode)
out = subprocess.check_output(['ssh', remote, f'cat {t}/out-{attempt}.log'], text=True)
time = subprocess.check_output(['ssh', remote, f'cat {t}/time-{attempt}.log'], text=True)
def val(pat):
    m = re.search(pat, time)
    return m.group(1) if m else None
r = dict(attempt=attempt, module=module, env='J', source_sha256=source_digest,
         source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
         deps_fingerprint=fp, dependency_objects=deps.splitlines(), source_path=str(src),
         exit=int(re.search(r'exit=(\d+)', out)[1]), wall=val(r'Elapsed.*: (\S+)'),
         peak_rss_kib=val(r'Maximum resident set size \(kbytes\): (\d+)'), swaps=val(r'Swaps: (\d+)'),
         output=out, timing=time, launcher=p.stdout)
with (root/'r1p-final/ser-join-attempts-8500-8599.jsonl').open('a') as f: f.write(json.dumps(r)+'\n')
raise SystemExit(r['exit'])
