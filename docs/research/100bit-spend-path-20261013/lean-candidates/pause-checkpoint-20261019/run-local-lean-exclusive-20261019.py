from pathlib import Path
import fcntl, os, subprocess, sys
# A shared OS lock serializes focused Lean while allowing every worker to
# prepare the next proof independently. Locks release automatically on exit.
if len(sys.argv) < 5:
    raise SystemExit('usage: runner.py MODULE FROZEN_SOURCE ATTEMPT EXISTING_RUNNER')
module, source, attempt, runner = sys.argv[1:]
if not Path(runner).is_file() or not Path(source).is_file():
    raise SystemExit('missing frozen source or existing focused runner')
with open('/tmp/aspis-focused-local-lean-20261019.lock', 'a+') as lock:
    print('Waiting for exclusive focused Lean slot:', module, flush=True)
    fcntl.flock(lock, fcntl.LOCK_EX)
    print('Acquired focused Lean slot:', module, 'pid', os.getpid(), flush=True)
    raise SystemExit(subprocess.run([sys.executable, runner, module, source, attempt]).returncode)
