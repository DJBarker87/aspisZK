"""Concrete source-only user producer and parameterless root continuation.

No public entry calls these functions. Tests mock reads and the final backend;
there is no report/GO/manifest parameter at either entry.
"""
import os
import signal
import subprocess
import time
from SbfProducerLinux_capture import require, Denied
from SbfProducerRss_guard import Guard, inherited_limits, check_limits
import SbfProducer_observe as observation
import SbfProducer_process as proc
from SbfProducer_package import (approval, verify_package, journal, ENV, SUDO, UNIT)


def pins(approved, role):
    package = verify_package()
    require(dict(os.environ) == ENV == approved['env'], 'actual environment drift')
    limits = inherited_limits()
    check_limits(limits, approved['limits'][role])
    runtime = observation.runtime_pins()
    require(runtime == approved['host'][role], 'actual interpreter/stdlib/runtime drift')
    # The process-level observation pins cmdline/exe/maps/IDs/caps/limits too.
    row = proc.process(os.getpid(), role, approved['roles'][role])
    require(row['cgroup'] == '0::'+approved['scope_path']+'\n', 'exact own user unit')
    return dict(package=package, limits=limits, runtime=runtime, process=row)


def fresh(approved, role):
    """Full policy recomputation, before/after actual pins and controls.

    The only truth inspected below comes from the exact copied collector,
    which itself invokes scans, visibility and evaluate. It is not an input.
    """
    start = time.monotonic()
    before = pins(approved, role)
    controls0 = observation.controls()
    observation.check_controls(controls0)
    report = observation.collect('inside-scope')
    controls1 = observation.controls()
    observation.check_controls(controls1)
    after = pins(approved, role)
    label = 'root' if role == 'helper' else 'user'
    journal(label+'-before.json', dict(pins=before, controls=controls0))
    journal(label+'-after.json', dict(pins=after, controls=controls1))
    require(before == after, 'source/runtime/environment/identity/inherited limits changed')
    decision = report['decision']
    require(report['api_version'] == 'SbfProducerRss20261025-v1' and
            decision['schema'] == 'ResourceStability20261025-v1' and
            decision['phase'] == 'inside-scope' and decision['additional_bytes'] == 0 and
            decision['allowed'] is True and 'error' not in decision and
            'collection_failures' not in decision, 'fresh full admission denied')
    bound = decision['scope_binding']
    require(bound['expected_limits'] == bound['observed_limits'] == observation.EXPECTED,
            'finite own 4GiB cap counted once')
    for observed in (controls0, controls1):
        actual = {k:v for k,v in observed['self_observation'].items() if k != 'reads'}
        require(actual == bound['self_identity'] == decision['collector_identity'], 'admission/control collector drift')
        require(actual['pid'] == os.getpid() == report['collector_pid'] and
                actual['unified_path'] == approved['scope_path'] and
                actual['path'].endswith('/'+UNIT+'.scope'), 'actual own scope binding')
    require(0 <= time.monotonic()-start < 110, 'stale scan/deadline')
    return before


def root_continuation():
    """Fixed operation, no arguments; all metadata FDs close before setup."""
    require(os.getresuid() == os.getresgid() == (0,0,0), 'root continuation IDs')
    approved = approval()
    before = proc.lineage(approved)
    fresh(approved, 'helper')
    require(before == proc.lineage(approved), 'sudo/monitor/helper transition drift')
    # Pin all guest physical sources to the root-owned published package; user
    # staging paths are never promoted to immutable root-owned sources.
    from SbfProducer_package import PACKAGE, pinned_file
    from SbfProducer_backend_candidate import validate_runtime
    manifest = approved['runtime']
    validate_runtime(manifest)
    for row in manifest['files']:
        require(row['physical'].startswith(PACKAGE+'/runtime/'), 'root runtime package path')
        pinned_file(row['physical'], {k:row[k] for k in ('sha256','size')}, row['mode'])
    require(before == proc.lineage(approved), 'prebackend lineage drift')
    require(pins(approved, 'helper')['process'] == before[-1], 'helper prebackend drift')
    # Concrete fixed body, no callback premise, runtime argument or flag enables
    # public CLI. This gate is the only candidate caller of the native body.
    from SbfProducer_backend_candidate import producer_fixed_body
    return producer_fixed_body()


def user_producer():
    require(os.getresuid() == os.getresgid() == (1000,1000,1000), 'fixed collector IDs')
    approved = approval()
    notifyfd = os.pidfd_open(os.getpid())
    guard = Guard(notify=lambda: signal.pidfd_send_signal(notifyfd, signal.SIGUSR1))
    observation.ACTIVE_GUARD = guard
    old = signal.getsignal(signal.SIGUSR1)
    signal.signal(signal.SIGUSR1, lambda *_: (_ for _ in ()).throw(Denied('resident guard failed')))
    failed = True
    child = None
    try:
        guard.start()
        before = fresh(approved, 'collector')
        guard.check()
        # Fixed literal sudo command only; no stdin, arbitrary output, retries,
        # shell, user environment forwarding or scope creation here.
        child = subprocess.Popen(SUDO, stdin=subprocess.DEVNULL,
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                 env=ENV, close_fds=True)
        code = child.wait(timeout=115)
        guard.check()
        require(code == 0, 'root continuation failed')
        require(pins(approved, 'collector') == before, 'producer changed during helper')
        failed = False
        return 0
    finally:
        try:
            if failed and child is not None:
                # Guard cancellation opens stable handles before checking the
                # retained start identities. Permission failures are retained;
                # waiting for our direct sudo child may be unbounded (OPEN).
                guard.cancel_owned()
                child.wait()
            if guard.thread is not None:
                journal('user-guard.json', guard.finish(failed=failed))
        finally:
            observation.ACTIVE_GUARD = None
            signal.signal(signal.SIGUSR1, old)
            os.close(notifyfd)
