#!/usr/bin/env python3
"""One sequential, fail-fast terminal dependency build inside a capped scope.

Does not edit retained sources or replace existing objects. Invoked only on host.
"""
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

W = Path(__file__).resolve().parent
BASE = Path('/home/dombarker/project-offloads')
J = BASE / 'aspis-joint-20261019'
env = json.loads((BASE / 'r1-privacy-build-integration-20261019/env/J.json').read_text())
manifest = json.loads((W / 'preflight-expanded.json').read_text())
BUILD = 'BUILD-53-2'
revision = (W / 'revision.txt').read_text().strip()
objects = W.parent / 'objects'
objects.mkdir(exist_ok=True)
IU = BASE / 'codex-cx-import-union-20261022'
paths = [objects, IU / 'objects', IU / 'retained-objects', J / 'objects'] + [Path(p) for p in env['LEAN_PATH'].split(':')]
sources = manifest['resolved_sources']
ordered, visiting, done, external = [], set(), set(), {}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def obj(m):
    return next((p / (m.replace('.', '/') + '.olean') for p in paths
                 if (p / (m.replace('.', '/') + '.olean')).is_file()), None)

def visit(m):
    if m in done:
        return
    if m in visiting:
        raise RuntimeError('import cycle: ' + m)
    if obj(m):
        done.add(m)
        return
    visiting.add(m)
    if m in sources:
        rec = sources[m]
        p = W / 'pinned' / rec['path']
        if sha(p) != rec['sha256']:
            raise RuntimeError('source pin mismatch: ' + m)
        root = max((W / 'pinned' / r for r in manifest['resolution_roots']
                    if str(p).startswith(str(W / 'pinned' / r) + '/')), key=lambda r: len(str(r)))
        imports = rec['imports']
    else:
        rel = m.replace('.', '/') + '.lean'
        candidates = [J / 'sources' / rel]
        # The already-audited arithmetic port owns these two generated modules.
        # Its port-summary.json records their successful 4.32 source hashes.
        if m in ['AspisR1SelectedMaskProbe.Funs', 'AspisR1SelectedMaskProbe.Types']:
            candidates.append(BASE / 'aspis-r1-mask-lean432-20261015/sources' / rel)
        p = next((q for q in candidates if q.is_file()), None)
        if p is None:
            raise RuntimeError('unresolved uncached import: ' + m)
        # Read-only retained shared source; preserve a pinned copy before building.
        import re
        imports = []
        for line in p.read_text().splitlines():
            hit = re.match(r'^\s*import\s+(.+)', line)
            if hit:
                imports.extend(hit[1].split('--')[0].split())
        target = W / 'external' / (m.replace('.', '/') + '.lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(p.read_bytes())
        origin = str(p)
        p, root = target, W / 'external'
        external[m] = {'origin': origin, 'sha256': sha(p), 'imports': imports}
    for i in imports:
        visit(i)
    ordered.append((m, p, root, imports))
    visiting.remove(m)
    done.add(m)

for m in manifest['roots']:
    visit(m)
(W / 'plan.json').write_text(json.dumps({
    'revision': revision, 'targets': manifest['roots'],
    'ordered_missing_modules': [x[0] for x in ordered], 'external_sources': external,
    'environment': env, 'limits': {'MemoryHigh': '6G', 'MemoryMax': '8G',
                                  'MemorySwapMax': 0, 'TasksMax': 64}}, indent=2))
print(BUILD, 'preflight complete:', len(ordered), 'missing modules', flush=True)
if '--check' in sys.argv:
    sys.exit(0)

# Read cgroup v2 aggregate usage, including every compiler child.
cgname = next(l.split('::', 1)[1] for l in Path('/proc/self/cgroup').read_text().splitlines()
              if '::' in l)
cg = Path('/sys/fs/cgroup') / cgname.lstrip('/')
def cgvalue(name):
    p = cg / name
    return int(p.read_text()) if p.exists() else None

actual = {n: (cg / n).read_text().strip() for n in
          ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max']}
(W / 'cgroup.json').write_text(json.dumps({'path': str(cg), 'actual': actual}, indent=2))
assert actual == {'memory.high': '6442450944', 'memory.max': '8589934592',
                  'memory.swap.max': '0', 'pids.max': '64'}, actual
runenv = os.environ.copy()
for k, v in env.items():
    if v is None:
        runenv.pop(k, None)
    else:
        runenv[k] = v
runenv['LEAN_PATH'] = ':'.join(map(str, paths))
runenv['RUSTFLAGS'] = '-C link-arg=-Wl,--threads=4'
build_start = time.monotonic()
result = 0
for index, (m, p, root, imports) in enumerate(ordered, 1):
    if obj(m):
        raise RuntimeError('object appeared after plan; stop rather than overwrite: ' + m)
    label = BUILD + '-' + str(index).zfill(3)
    fingerprint = hashlib.sha256(json.dumps(
        [(i, str(obj(i)), sha(obj(i))) for i in imports], sort_keys=True).encode()).hexdigest()
    output = objects / (m.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    log, timing = W / (label + '.log'), W / (label + '.time')
    cmd = [env['LEAN'], '-j1', '-M7000', '-DElab.async=false', '-R', str(root),
           '-o', str(output), str(p)]
    start = time.monotonic()
    peak_rss, peak_current, reason = 0, 0, None
    print(label, m, flush=True)
    with log.open('w') as out:
        proc = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(timing)] + cmd,
                                env=runenv, stdout=out, stderr=subprocess.STDOUT,
                                start_new_session=True)
        last_notice = start
        while proc.poll() is None:
            rss = 0
            for f in cg.glob('cgroup.procs'):
                for pid in f.read_text().split():
                    try:
                        status = Path('/proc') / pid / 'status'
                        rss += next(int(l.split()[1]) * 1024 for l in status.read_text().splitlines()
                                    if l.startswith('VmRSS:'))
                    except (FileNotFoundError, ProcessLookupError, StopIteration):
                        pass
            peak_rss = max(peak_rss, rss)
            current = cgvalue('memory.current')
            peak_current = max(peak_current, current or 0)
            if rss >= 7.5 * 1024**3 or time.monotonic() - start >= 600:
                reason = 'aggregate RSS near cap' if rss >= 7.5 * 1024**3 else 'ten minutes without compiled target'
                os.killpg(proc.pid, 15)
                break
            if time.monotonic() - last_notice >= 30:
                print(label, 'elapsed', round(time.monotonic() - start),
                      'aggregate_RSS', rss, 'memory.current', current, flush=True)
                last_notice = time.monotonic()
            time.sleep(0.25)
        try:
            rc = proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, 9)
            rc = proc.wait()
    text = log.read_text()
    record = {'build': BUILD, 'label': label, 'module': m, 'command': cmd,
              'revision': revision, 'source_sha256': sha(p), 'deps_fingerprint': fingerprint,
              'exit': rc, 'wall_seconds': time.monotonic() - start,
              'aggregate_peak_rss_bytes_sampled': peak_rss,
              'peak_memory_current_bytes_sampled': peak_current,
              'cgroup_memory_peak_bytes': cgvalue('memory.peak'),
              'cgroup_swap_current_bytes': cgvalue('memory.swap.current'),
              'axioms_output': [l for l in text.splitlines() if 'axioms' in l],
              'axioms_note': 'Retained dependency; no new theorem. Full output preserved.',
              'stop_reason': reason}
    with (W / 'modules.jsonl').open('a') as f:
        f.write(json.dumps(record) + '\n')
    print(label, 'exit', rc, 'wall', round(record['wall_seconds'], 2), flush=True)
    if rc != 0 or reason:
        print(text[-8000:], flush=True)
        result = rc or 1
        break
(W / 'result.json').write_text(json.dumps({
    'label': BUILD, 'target': manifest['roots'], 'exit': result,
    'wall_seconds': time.monotonic() - build_start, 'revision': revision,
    'cgroup_memory_peak_bytes': cgvalue('memory.peak'),
    'cgroup_swap_current_bytes': cgvalue('memory.swap.current'),
    'memory_events': (cg / 'memory.events').read_text()}, indent=2))
sys.exit(result)
