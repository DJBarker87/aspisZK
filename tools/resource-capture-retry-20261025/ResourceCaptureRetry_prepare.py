"""Materialize only the immutable source plus the reviewed retry wrapper."""
import subprocess
from pathlib import Path
REV = '9fe9f199d1e52e3dcf4b355dff57330e5019a220'
PATH = 'tools/resource-snapshot-20261025/ResourceSnapshot_candidate.py'
base = subprocess.check_output(['git', 'show', REV+':'+PATH]).decode()
wrapper = '''def scan(root=Path('/sys/fs/cgroup')):
    """Bounded fresh metadata scans; failed raw captures are not retained/reused.

    Only compact failure provenance survives; no failed epoch supplies GO inputs.
    This refresh is not an atomic-state, safety, termination or crypto proof.
    """
    failures = []
    for attempt in range(1, 5):
        try:
            snapshot = scan_once(root)
        except OSError as exc:
            path = exc.filename
            parts = path.split('/') if isinstance(path, str) else []
            retryable = (exc.errno in (2, 3) and len(parts) == 4
                         and parts[:2] == ['', 'proc']
                         and parts[2].isascii() and parts[2].isdecimal()
                         and parts[2][0] in '123456789'
                         and parts[3] in ('stat', 'status', 'cgroup'))
            if not retryable:
                raise
            failures.append(dict(attempt=attempt, errno=exc.errno, path=path,
                                 type=type(exc).__name__, discarded_all_inputs=True))
            # Original scan annotates errors with potentially large partial data.
            # Drop it and its scan frames, including on terminal exhaustion.
            exc.__dict__.clear()
            exc.__traceback__ = None
            if attempt == 4:
                exc.discarded_scan_failures = failures
                raise exc.with_traceback(None) from None
        else:
            snapshot['discarded_scan_failures'] = failures
            snapshot['discarded_all_inputs'] = True
            return snapshot


'''
assert base.count('def scan(root=') == 1
candidate = base.replace('def scan(root=', 'def scan_once(root=', 1)
candidate = candidate.replace('def validate_membership(snapshot):', wrapper+'def validate_membership(snapshot):', 1)
Path(__file__).with_name('ResourceCaptureRetry_candidate.py').write_text(candidate)
