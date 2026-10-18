#!/usr/bin/env python3
"""Coordinate focused A leaves with the host's existing lead Lean lock."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

W = Path('/home/dombarker/project-offloads/aspis-r1-worker-a-rounds-proof-20261017')
REV = 'a555c852664c80000942f0c911e16719a5493625'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('module')
    ap.add_argument('attempt')
    ap.add_argument('--locked', action='store_true')
    a = ap.parse_args()
    entry = W / 'runs' / (a.attempt + '-queue.json')
    now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
    if not a.locked:
        command = ['flock', '-w', '45', '-E', '75', '/tmp/aspis-r0-lean.lock',
                   sys.executable, str(Path(__file__).resolve()), a.module, a.attempt, '--locked']
        receipt = {'requested_utc': now(), 'command': command, 'source_revision': REV,
                   'launcher_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   'lock': '/tmp/aspis-r0-lean.lock', 'maximum_queue_seconds': 45}
        entry.write_text(json.dumps(receipt, indent=2) + '\n')
        start = time.monotonic()
        with (W / 'runs' / (a.attempt + '-launch.log')).open('w') as log:
            exit_status = subprocess.call(command, stdout=log, stderr=subprocess.STDOUT)
        receipt.update(exit_status=exit_status, queued_and_run_seconds=time.monotonic() - start,
                       finished_utc=now())
        entry.write_text(json.dumps(receipt, indent=2) + '\n')
        return exit_status
    scopes = []
    parent = Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice')
    for scope in parent.glob('*.scope'):
        try:
            pids = [x for p in scope.rglob('cgroup.procs') for x in p.read_text().split()]
            maximum = (scope / 'memory.max').read_text().strip()
            if pids and maximum != 'max':
                scopes.append({'scope': str(scope), 'memory_max': int(maximum), 'pids': pids})
        except FileNotFoundError:
            pass
    reserved = sum(s['memory_max'] for s in scopes)
    assert reserved + 8 * 2**30 < 55 * 2**30, scopes
    manifest = W / 'input-manifest.json'
    data = json.loads(manifest.read_text())
    data['sources'] = {str(p.relative_to(W / 'sources')): hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in (W / 'sources').rglob('*.lean')}
    manifest.write_text(json.dumps(data, indent=2) + '\n')
    command = ['systemd-run', '--user', '--scope', '--unit=aspis-a-' + a.attempt,
               '-p', 'MemoryHigh=6G', '-p', 'MemoryMax=8G', '-p', 'MemorySwapMax=0',
               sys.executable, str(W / 'run-lean-host.py'), str(W), a.module,
               '--attempt', a.attempt, '--revision', REV]
    (W / 'runs' / (a.attempt + '-lock-acquired.json')).write_text(json.dumps({
        'acquired_utc': now(), 'command': command, 'source_revision': REV,
        'active_capped_scopes': scopes, 'reserved_memory_max_bytes': reserved,
        'own_memory_max_bytes': 8 * 2**30, 'safe_limit_bytes': 55 * 2**30,
        'lock_held_by_parent_flock_until_child_exit': True}, indent=2) + '\n')
    return subprocess.call(command)


if __name__ == '__main__':
    sys.exit(main())
