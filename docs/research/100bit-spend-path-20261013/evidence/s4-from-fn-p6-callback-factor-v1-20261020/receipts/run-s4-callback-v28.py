from pathlib import Path
import json, os, subprocess, sys, hashlib, time
lock = Path('/tmp/aspis-local-lean.lock.d')
target = 'S4GeneratedCallbackClosurePreservationV28'
try:
    lock.mkdir()
except FileExistsError:
    raise SystemExit('lock occupied; no Lean started')
owner = lock / 'owner.json'
owner.write_text(json.dumps({'target': target, 'pid': os.getpid()}))
try:
    lines = subprocess.check_output(['ps', '-axo', 'pid=,comm='], text=True).splitlines()
    live = []
    for line in lines:
        p = line.strip().split(None, 1)
        if len(p) == 2 and Path(p[1]).name == 'lean':
            live.append(p[0])
    if live:
        raise SystemExit('live Lean exists; no Lean started: ' + ','.join(live))
    lean = '/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
    source = '/tmp/S4GeneratedCallbackClosurePreservationV28.lean'
    obj = '/tmp/s4-p6-clean-repair-compile/S4GeneratedCallbackClosurePreservationV28.olean'
    log = '/tmp/s4-p6-clean-repair-compile/closure-v45.log'
    env = dict(os.environ)
    env['LEAN_PATH'] = '/tmp/s4-p6-clean-repair-compile:/tmp/s4-p6-formatter-repair-closure:/tmp/lean432-nuc-aeneas-cache:/Users/dominic/ZK/AspisFormal/.lake/packages/Cli/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/packages/batteries/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/packages/Qq/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/packages/aesop/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/packages/proofwidgets/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/packages/importGraph/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/packages/plausible/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/packages/mathlib/.lake/build/lib/lean:/Users/dominic/ZK/AspisFormal/.lake/build/lib/lean:/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'
    cmd = ['/usr/bin/time', '-l', lean, '-j1', '-M', '4400', '-R', '/tmp', source, '-o', obj]
    Path(log).parent.mkdir(parents=True, exist_ok=True)
    with open(log, 'w') as f:
        rc = subprocess.run(cmd, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
    print(Path(log).read_text())
    raise SystemExit(rc)
finally:
    try:
        current = json.loads(owner.read_text())
        if current == {'target': target, 'pid': os.getpid()}:
            owner.unlink()
            lock.rmdir()
    except (FileNotFoundError, OSError, json.JSONDecodeError):
        pass
