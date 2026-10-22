#!/usr/bin/env python3
"""Sequential, capped import-union rebuild; preserves all shared objects.

plan.json pins sources/Module.lean and lists targets bottom-up. Each successful
unchanged source+direct-object fingerprint is reused. Failed unchanged inputs
are refused. Run only inside the launcher's verified 6G/8G/zero-swap scope.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

W = Path(__file__).resolve().parent
E = W / 'evidence'
E.mkdir(exist_ok=True)
plan = json.loads((W / 'plan.json').read_text())
env = os.environ.copy()
for k, v in plan['environment'].items():
    if v is None:
        env.pop(k, None)
    else:
        env[k] = v
paths = [W / 'objects'] + [Path(p) for p in plan['lean_paths']]
env['LEAN_PATH'] = ':'.join(map(str, paths))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def obj(m):
    return next((p / (m.replace('.', '/') + '.olean') for p in paths
                 if (p / (m.replace('.', '/') + '.olean')).is_file()), None)

cgname = next(l.split('::', 1)[1] for l in Path('/proc/self/cgroup').read_text().splitlines() if '::' in l)
cg = Path('/sys/fs/cgroup') / cgname.lstrip('/')
actual = {n: (cg / n).read_text().strip() for n in ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max']}
assert actual == {'memory.high': '6442450944', 'memory.max': '8589934592', 'memory.swap.max': '0', 'pids.max': '64'}, actual
(E / 'cgroup.json').write_text(json.dumps({'path': str(cg), 'actual': actual}, indent=2) + '\n')
def cgval(n):
    return int((cg / n).read_text())
records = [json.loads(l) for l in (E / 'modules.jsonl').read_text().splitlines()] if (E / 'modules.jsonl').exists() else []
only = sys.argv[2] if len(sys.argv) == 3 and sys.argv[1] == '--only' else None
start_build = time.monotonic()
rc = 0
for rec in plan['ordered']:
    m = rec['module']
    if only and m != only:
        continue
    p = W / 'sources' / (m.replace('.', '/') + '.lean')
    assert sha(p) == rec['sha256'], m
    deps = [(i, str(obj(i)), sha(obj(i))) for i in rec['imports']]
    fingerprint = hashlib.sha256(json.dumps(deps, sort_keys=True).encode()).hexdigest()
    previous = [r for r in records if r['module'] == m and r['source_sha256'] == sha(p) and r['deps_fingerprint'] == fingerprint]
    if previous:
        r = previous[-1]
        if r['exit'] == 0 and obj(m) == W / 'objects' / (m.replace('.', '/') + '.olean') and sha(obj(m)) == r['object_sha256']:
            print('REUSE', r['label'], m, flush=True)
            continue
        raise RuntimeError('Refuse unchanged failed/missing-artifact attempt: ' + m)
    label = 'IU-' + str(1 + max([int(r['label'].split('-')[1]) for r in records], default=0))
    output = W / 'objects' / (m.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    log, timing = E / (label + '.log'), E / (label + '.time')
    cmd = [env['LEAN'], '-j1', '-M7000', '-DElab.async=false', '-R', str(W / 'sources'), '-o', str(output), str(p)]
    print(label, m, flush=True)
    start = time.monotonic()
    peak_rss, reason = 0, None
    with log.open('w') as out:
        proc = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(timing)] + cmd, env=env, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
        notice = start
        while proc.poll() is None:
            rss = 0
            for pid in (cg / 'cgroup.procs').read_text().split():
                try:
                    rss += next(int(l.split()[1])*1024 for l in (Path('/proc') / pid / 'status').read_text().splitlines() if l.startswith('VmRSS:'))
                except (FileNotFoundError, ProcessLookupError, StopIteration):
                    pass
            peak_rss = max(rss, peak_rss)
            if rss >= 7.5*1024**3 or time.monotonic() - start >= 600:
                reason = 'aggregate RSS near cap' if rss >= 7.5*1024**3 else 'ten minutes without compiled target'
                os.killpg(proc.pid, signal.SIGTERM)
                break
            if time.monotonic() - notice > 30:
                print(label, 'elapsed', round(time.monotonic()-start), 'aggregate RSS', rss, flush=True)
                notice = time.monotonic()
            time.sleep(0.25)
        try:
            rc = proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            rc = proc.wait()
    text = log.read_text()
    r = {'label': label, 'module': m, 'command': cmd, 'lean_path': env['LEAN_PATH'],
         'source_revision': plan['revision'], 'source_sha256': sha(p), 'deps': deps,
         'deps_fingerprint': fingerprint, 'exit': rc, 'wall_seconds': time.monotonic()-start,
         'aggregate_peak_rss_bytes_sampled': peak_rss,
         'cgroup_memory_peak_bytes': cgval('memory.peak'), 'swap_bytes': cgval('memory.swap.current'),
         'axioms_output': [l for l in text.splitlines() if 'axioms' in l],
         'object_sha256': sha(output) if rc == 0 else None, 'stop_reason': reason}
    with (E / 'modules.jsonl').open('a') as f:
        f.write(json.dumps(r, sort_keys=True) + '\n')
    records.append(r)
    print(label, 'exit', rc, 'wall', round(r['wall_seconds'], 2), flush=True)
    if rc or reason:
        print(text[-6000:], flush=True)
        rc = rc or 1
        break
(E / ('focused-result.json' if only else 'result.json')).write_text(json.dumps({
    'targets': [only] if only else plan['targets'], 'exit': rc, 'wall_seconds': time.monotonic()-start_build,
    'source_revision': plan['revision'], 'cgroup_memory_peak_bytes': cgval('memory.peak'),
    'swap_bytes': cgval('memory.swap.current'), 'memory_events': (cg / 'memory.events').read_text()}, indent=2) + '\n')
sys.exit(rc)
