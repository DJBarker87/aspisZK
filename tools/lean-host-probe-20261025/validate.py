"""Bounded local test receipt; starts only the local Python fixture test suite."""
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).absolute().parent
EVIDENCE = ROOT.parent.parent / 'evidence/lean-host-probe-20261025'


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(65536), b''): h.update(b)
    return h.hexdigest()


if __name__ == '__main__':
    label = sys.argv[1]
    if not label.isalnum(): raise SystemExit('alphanumeric fresh receipt label required')
    argv = [sys.executable, '-I', '-B', str(ROOT/'test_probe.py')]
    sources = {p.name: {'sha256': sha(p), 'size': p.stat().st_size}
               for p in sorted(ROOT.iterdir()) if p.is_file()}
    started = time.monotonic()
    run = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
                         env={'PATH': '/usr/bin:/bin', 'PYTHONDONTWRITEBYTECODE': '1'})
    wall = time.monotonic()-started
    own = resource.getrusage(resource.RUSAGE_SELF)
    child = resource.getrusage(resource.RUSAGE_CHILDREN)
    # Darwin ru_maxrss is bytes; Linux is KiB. These are separate high water marks.
    scale = 1 if sys.platform == 'darwin' else 1024
    receipt = {'target': 'local fixture and mock tests only', 'argv': argv,
               'source_revision': 'b2c335bc89bb5dba0389d34b057bf22689ada592 + source hashes below',
               'sources': sources, 'exit': run.returncode, 'wall_seconds': wall,
               'self_peak_rss_bytes': own.ru_maxrss*scale,
               'child_peak_rss_bytes': child.ru_maxrss*scale,
               'sum_of_separate_peak_rss_bytes': (own.ru_maxrss+child.ru_maxrss)*scale,
               'self_swap_counter': own.ru_nswap, 'child_swap_counter': child.ru_nswap,
               'swap_bytes': 'not available from getrusage; no swap settings changed',
               'axioms': 'N/A: no Lean invocation/theorem',
               'python': {'executable': sys.executable, 'sha256': sha(sys.executable),
                          'version': sys.version, 'trusted_boundary': 'local CPython/OS'},
               'host_actions': 0, 'lean_calls': 0, 'ssh_calls': 0,
               'stdout': run.stdout.decode(), 'stderr': run.stderr.decode()}
    # Record concrete loaded Python dependency sources; builtins have no file bytes.
    receipt['loaded_runner_dependencies'] = {
        name: {'path': m.__file__, 'sha256': sha(m.__file__)}
        for name, m in sorted(sys.modules.items())
        if isinstance(getattr(m, '__file__', None), str) and Path(m.__file__).is_file()
        and name != '__main__'}
    path = EVIDENCE / ('validation-'+label+'.json')
    with path.open('x') as f: json.dump(receipt, f, indent=2, sort_keys=True); f.write('\n')
    print(json.dumps({'receipt': str(path), 'exit': run.returncode, 'wall_seconds': wall,
                      'sum_separate_peaks_bytes': receipt['sum_of_separate_peak_rss_bytes']}))
    raise SystemExit(run.returncode)
