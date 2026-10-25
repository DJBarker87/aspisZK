"""Prospective v6 LOCAL collector; main disabled, no Popen/SSH entry allocated.
Exclusive owner of an unreaped Popen; no external wait/reaper is permitted.
Command labels never establish identity. No remote cleanup conclusion.
"""
import json
import hashlib
import subprocess
import sys
import os
import time
from pathlib import Path

RELEASE = Path('tools/prover-rw-20261023/final-native-gate/prospective-data-v10')
CAPTURE = Path('/private/tmp/FinalNativeGateV10-future-capture-029')
ARGV = ['python3', '-B', str(RELEASE/'FinalNativeGate-data-transport.py')]
FUTURE_ALLOCATION = None  # No main/conditional SSH allocation in this source job.
PINS = {'transfer_manifest_root': '3ba20eca415432d587c8a22ee7b38bedeced844b532d95ed60a8c49fafe33d1f', 'files': {'FinalNativeGate-data-transfer.py': {'size': 910190, 'sha256': '2fea5c04ce3f323b0c80c878f51064ad1dbc338855c49668c34834779dd3ec81'}, 'FinalNativeGate-data-transport.py': {'size': 3855, 'sha256': '5d37bd8c81e35a12e0e80b882572e55d5e0e0f22170742eeff0c437284525cf3'}, 'FinalNativeGate-release-identities.json': {'size': 36538, 'sha256': 'e17502462f01ecefbfd48775888a93037c072b5bfca1fbed6cf012c0fab30ec4'}}}
HARD = ('pid', 'ppid', 'uid', 'pgid', 'start')


def identity(row):
    value = tuple(row[k] for k in HARD)
    if any(x is None for x in value) or type(row['pid']) is not int or row['pid'] <= 0 or any(type(row[k]) is not int or row[k] < 0 for k in ('ppid','uid','pgid')):
        raise ValueError('malformed hard identity')
    if not isinstance(row['start'], str) or not row['start']:
        raise ValueError('missing birth start')
    return value


def parse_ps(text):
    """ps pid=,ppid=,uid=,pgid=,rss=,lstart=,comm=; failure is never absence."""
    rows = {}
    for line in text.splitlines():
        w = line.split(None, 10)
        if len(w) != 11:
            raise ValueError('process sample shape')
        row = dict(pid=int(w[0]), ppid=int(w[1]), uid=int(w[2]), pgid=int(w[3]),
                   rss_bytes=int(w[4])*1024, start=' '.join(w[5:10]), command=w[10])
        # Unselected kernel/system metadata may legitimately contain PID/UID zero.
        if any(row[k] < 0 for k in ('pid','ppid','uid','pgid')):
            raise ValueError('negative process metadata')
        if row['rss_bytes'] < 0 or row['pid'] in rows:
            raise ValueError('invalid/duplicate RSS row')
        rows[row['pid']] = row
    return rows


class Snapshot(dict):
    reaped_sampler = None


def snapshot():
    # Exact owned metadata child only; no transport/native Popen entry exists.
    child = subprocess.Popen(['/bin/ps', '-axo', 'pid=,ppid=,uid=,pgid=,rss=,lstart=,comm='],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        out, err = child.communicate(timeout=2)
        if child.returncode != 0:
            raise RuntimeError('ps failure '+str(child.returncode)+': '+err)
        rows = Snapshot(parse_ps(out))
        rows.reaped_sampler = child.pid
        return rows
    finally:
        # This Popen is exclusively owned and unreaped until communicate/wait.
        original = repr(sys.exc_info()[1])
        errors = []
        try:
            if child.poll() is None:
                child.kill()
        except Exception as exc:
            errors.append('ps control: '+repr(exc))
        finally:
            try:
                child.wait(timeout=3)
            except Exception as exc:
                errors.append('ps reap: '+repr(exc))
        if errors:
            raise RuntimeError('ps ownership/reap unresolved: '+repr(errors)+'; original='+original)


def pin(path):
    raw = Path(path).read_bytes()
    return dict(size=len(raw), sha256=hashlib.sha256(raw).hexdigest())


def validate_release():
    if PINS is None:
        raise ValueError('v6 pins not prepared')
    identities = json.loads((RELEASE/'FinalNativeGate-release-identities.json').read_bytes())
    for name, expected in PINS['files'].items():
        if pin(RELEASE/name) != expected:
            raise ValueError('fixed v6 source pin: '+name)
    if identities['transfer_manifest_root'] != PINS['transfer_manifest_root']:
        raise ValueError('fixed v6 transfer root')
    if {p.name for p in (RELEASE/'payload').iterdir()} != set(identities['transfer_manifest']):
        raise ValueError('v6 exact payload coverage')
    for name, expected in identities['transfer_manifest'].items():
        if pin(RELEASE/'payload'/name) != expected:
            raise ValueError('v6 payload pin: '+name)
    return identities


def future_precharge(ledger_path):
    # No invocation now. A later allocation/source review must bind this field.
    if FUTURE_ALLOCATION is None:
        raise ValueError('no future caller allocation')
    validate_release()
    CAPTURE.mkdir(mode=0o700, exist_ok=False)
    exclusive_charge(CAPTURE/'main-exclusive-charge.json', pin(ledger_path))
    return list(ARGV)


def exclusive_charge(path, ledger_pin):
    # Future allocation only. Exclusive marker is written BEFORE any eventual spawn.
    with Path(path).open('x') as stream:
        json.dump(dict(main_precharged=1, ledger_pin=ledger_pin,
                       execution_authority=False), stream)
        stream.flush(); os.fsync(stream.fileno())


class Collector:
    def __init__(self, child, snapshot, output_bytes, clock=time.monotonic,
                 parent_pid=None, uid=None):
        self.child = child
        self.snapshot = snapshot
        self.output_bytes = output_bytes
        self.clock = clock
        self.started = clock()
        self.parent_pid = os.getpid() if parent_pid is None else parent_pid
        self.uid = os.getuid() if uid is None else uid
        self.rc = None
        self.reaped = False
        self.root = None
        self.owned = {}
        self.samples = []
        self.errors = []
        self.control_needed = None
        self.control_attempted = False

    def observe_exit(self):
        code = self.child.poll()
        if code is not None:
            self.rc = code  # Persist before any wait/snapshot/publication failure.
            self.rc = self.child.wait(timeout=3)
            self.reaped = True
            return True
        return False

    def sample(self):
        if self.observe_exit():
            self.control_needed = False
            return False
        rows = self.snapshot()  # Exceptions preserve partial evidence; never empty fallback.
        ended = self.observe_exit()  # Close the poll-to-scan exit window, no retry loop.
        root = rows.get(self.child.pid)
        if not ended:
            if root is None:
                raise ValueError('live owned root visibility unknown')
            birth = identity(root)
            if self.root is None:
                if (root['ppid'], root['uid'], root['pgid']) != (self.parent_pid, self.uid, self.child.pid):
                    raise ValueError('owned root hard identity mismatch')
                self.root = birth
            elif birth != self.root:
                raise ValueError('owned root birth/hard identity drift')
            self.owned[self.child.pid] = self.root
        retained = set(self.owned)
        selected = {self.parent_pid} | retained | {self.child.pid}
        previous = None
        while previous != selected:
            previous = set(selected)
            selected.update(p for p, r in rows.items() if r['ppid'] in selected)
        observed = []
        for pid in sorted(selected & rows.keys()):
            row = rows[pid]
            if pid == self.child.pid and ended:
                # A post-reap row could be reused. Retain as uncharged ambiguous raw data.
                continue
            birth = identity(row)
            if pid in self.owned and birth != self.owned[pid]:
                raise ValueError('retained child hard identity drift/reuse')
            if pid != self.parent_pid and pid != getattr(rows, 'reaped_sampler', None):
                self.owned[pid] = birth
            observed.append(row)
        missing = sorted(retained - rows.keys() - {self.child.pid})
        total = sum(row['rss_bytes'] for row in observed)
        self.samples.append(dict(elapsed=self.clock()-self.started, rss_bytes=total,
                                 processes=observed, scan_root=root, root_already_exited=ended,
                                 missing_retained=missing, metrics_complete=not missing,
                                 reaped_sampler=getattr(rows, 'reaped_sampler', None)))
        if missing:
            raise ValueError('retained descendants visibility unresolved')
        if total >= 512*2**20:
            raise MemoryError('sampled aggregate512MiB ceiling')
        if self.output_bytes() > 4*2**20:
            raise ValueError('caller public output4MiB ceiling')
        if self.clock()-self.started > 135:
            raise TimeoutError('caller135s deadline; SSH transport remains120s')
        self.control_needed = not ended
        return not ended

    def finish(self):
        """Always invoked in eventual caller finally. Keep child until actual reap."""
        try:
            if self.observe_exit():
                self.control_needed = False
                return
            self.control_needed = True
            rows = self.snapshot()
            if self.observe_exit():
                self.control_needed = False
                return
            root = rows.get(self.child.pid)
            if self.root is None or root is None or identity(root) != self.root:
                raise ValueError('cleanup root identity unresolved; no signal')
            # Only direct unreaped owned Popen. No killpg or descendant PID signalling.
            self.control_attempted = True
            self.child.kill()
        except Exception as exc:
            self.errors.append('control/observation: '+repr(exc))
        finally:
            try:
                # Poll/reap once more even after snapshot/control failure.
                if not self.observe_exit():
                    self.rc = self.child.wait(timeout=3)
                    self.reaped = True
            except Exception as exc:
                self.errors.append('owned reap unresolved: '+repr(exc))

    def receipt(self):
        return dict(exit=self.rc, reaped=self.reaped, errors=self.errors, samples=self.samples,
                    owned_birth_identities=self.owned, control_needed=self.control_needed,
                    control_attempted=self.control_attempted,
                    descendant_control='UNRESOLVED: no stable descendant control handle allocated',
                    remote_cleanup='UNKNOWN', native_proof=False)


def collect_owned(child, output_bytes, emit, read_snapshot=snapshot):
    """Future entry calls only after exclusive charge and its own allocated Popen.
    No launch here; caller owns the child continuously through actual reap.
    """
    collector = Collector(child, read_snapshot, output_bytes)
    try:
        while collector.sample():
            time.sleep(.05)
    except BaseException as exc:
        collector.errors.append('collection: '+repr(exc))
    finally:
        collector.finish()
        emit(collector.receipt())  # rc persists even if collection/control failed.
    return collector.receipt()


def main():
    print('FinalNativeGate v6 caller SOURCE ONLY: disabled; future lead allocation required')
    return 78


if __name__ == '__main__':
    raise SystemExit(main())
