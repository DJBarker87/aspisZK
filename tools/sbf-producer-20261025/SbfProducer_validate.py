"""Run the single changed-source pure/mock suite with an in-process receipt."""
import hashlib
import io
import json
import os
from pathlib import Path
import resource
import sys
import time
import unittest

HERE = Path(__file__).resolve().parent
OUT = HERE.parents[1]/'evidence/sbf-producer-20261025'


def pin(path):
    raw = path.read_bytes()
    return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))


class Bounded(io.StringIO):
    def write(self, text):
        if self.tell()+len(text) > 16384:
            raise RuntimeError('test output exceeds 16KiB')
        return super().write(text)


if __name__ == '__main__':
    revision = sys.argv[1]
    require_revision = len(revision) == 40 and all(c in '0123456789abcdef' for c in revision)
    if not require_revision:
        raise SystemExit('exact source revision required')
    start = time.monotonic()
    stream = Bounded()
    import SbfProducer_tests
    followup = sys.argv[2:] == ['--fd-followup']
    package_followup = sys.argv[2:] == ['--package-followup']
    if sys.argv[2:] and not (followup or package_followup):
        raise SystemExit('unknown selection')
    label = ('SbfProducer-package-focused' if package_followup else
             'SbfProducer-fd-focused' if followup else 'SbfProducer-focused')
    if package_followup:
        names = ['test_exact_copy_and_operational_functions',
                 'test_inherited_descriptor_and_stdio_access_fail_closed',
                 'test_launcher_and_root_policy_are_pinned_by_live_reads']
        suite = unittest.TestSuite(SbfProducer_tests.Suite(name) for name in names)
    elif followup:
        names = ['test_exact_copy_and_operational_functions',
                 'test_launcher_and_root_policy_are_pinned_by_live_reads',
                 'test_inherited_descriptor_and_stdio_access_fail_closed',
                 'test_root_order_no_backend_on_any_guard_failure']
        suite = unittest.TestSuite(SbfProducer_tests.Suite(name) for name in names)
    else:
        suite = unittest.defaultTestLoader.loadTestsFromModule(SbfProducer_tests)
    result = unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
    elapsed = time.monotonic()-start
    usage = resource.getrusage(resource.RUSAGE_SELF)
    peak = usage.ru_maxrss*(1 if sys.platform == 'darwin' else 1024)
    passed = result.wasSuccessful() and peak < 512*2**20
    with (OUT/(label+'.log')).open('x') as f:
        f.write(stream.getvalue())
    dependencies = {}
    for name,module in sorted(sys.modules.items()):
        filename = getattr(module,'__file__',None)
        if filename and Path(filename).is_file() and Path(filename).suffix in ('.py','.so'):
            dependencies[name] = dict(path=filename,**pin(Path(filename)))
    receipt = dict(command=[sys.executable,*sys.orig_argv[1:]],
        source_revision=revision, source_overlay={p.name:pin(p) for p in sorted(HERE.iterdir()) if p.is_file()},
        exit=0 if passed else 1, wall_seconds=elapsed, peak_rss_bytes=peak,swap=usage.ru_nswap,
        interpreter=dict(path=sys.executable,version=sys.version,**pin(Path(sys.executable).resolve())),
        dependencies=dependencies, tests=result.testsRun, failures=len(result.failures),errors=len(result.errors),
        log=pin(OUT/(label+'.log')), print_axioms='N/A; no Lean/theorems',
        mode='PURE/EXPLICIT MOCKS ONLY; no backend/native/process/host operations',
        historical='SbfLinux 54 cases REUSED from 9f50be799e, not rerun; no old full report replay',
        host_budget_used=0, native_budget_used=0, source_only=True)
    with (OUT/(label+'-receipt.json')).open('x') as f:
        json.dump(receipt,f,sort_keys=True,indent=2);f.write('\n')
    print(stream.getvalue(),end='')
    print('peak_rss_bytes='+str(peak)+'; swap='+str(usage.ru_nswap))
    raise SystemExit(0 if passed else 1)
