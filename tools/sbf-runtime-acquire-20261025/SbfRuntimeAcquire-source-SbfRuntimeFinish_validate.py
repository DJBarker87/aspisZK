"""Single focused local source/synthetic-data suite; never imports payload."""
import hashlib
import io
import json
from pathlib import Path
import resource
import sys
import time
import unittest

HERE = Path(__file__).resolve().parent
OUT = HERE.parents[1]/'evidence/sbf-runtime-finish-20261025'

def pin(path):
    raw = path.read_bytes()
    return dict(size=len(raw), sha256=hashlib.sha256(raw).hexdigest())

if __name__ == '__main__':
    revision = sys.argv[1]
    if len(revision) != 40:
        raise SystemExit('exact source revision required')
    start = time.monotonic()
    import SbfRuntimeFinish_tests
    stream = io.StringIO()
    suite = unittest.defaultTestLoader.loadTestsFromModule(SbfRuntimeFinish_tests)
    names = [t.id() for group in suite for t in group]
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    usage = resource.getrusage(resource.RUSAGE_SELF)
    peak = usage.ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
    passed = result.wasSuccessful() and peak < 512*2**20
    (OUT/'SbfRuntimeFinish-tests.log').write_text(stream.getvalue())
    dependencies = {}
    for name, module in sorted(sys.modules.items()):
        file = getattr(module, '__file__', None)
        if file and Path(file).is_file():
            dependencies[name] = dict(path=file, **pin(Path(file)))
    receipt = dict(command=[sys.executable,*getattr(sys,'orig_argv',sys.argv)[1:]],
                   argv_source='sys.orig_argv' if hasattr(sys,'orig_argv') else 'sys.argv',
                   source_revision=revision, source_overlay={p.name:pin(p) for p in sorted(HERE.iterdir()) if p.is_file()},
                   dependencies=dependencies, interpreter=dict(path=sys.executable,version=sys.version,**pin(Path(sys.executable))),
                   exit=0 if passed else 1, wall_seconds=time.monotonic()-start, peak_rss_bytes=peak,
                   swap=usage.ru_nswap, aggregate_rss='single local fixture process; no children; peak process RSS above',
                   tests=result.testsRun, full_test_names=names, failures=len(result.failures),errors=len(result.errors),
                   log=pin(OUT/'SbfRuntimeFinish-tests.log'), print_axioms='N/A; no Lean/theorems',
                   reused='old trace and producer evidence immutable Git; historical suites NOT rerun',
                   actual_host_budget_used=0, payload_executed=False, mode='PURE_SOURCE_SYNTHETIC_FS_RETAINED_DATA_ONLY')
    (OUT/'SbfRuntimeFinish-tests-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(stream.getvalue(),end='')
    print(json.dumps(dict(exit=receipt['exit'],tests=result.testsRun,peak_rss_bytes=peak,swap=usage.ru_nswap)))
    raise SystemExit(receipt['exit'])
