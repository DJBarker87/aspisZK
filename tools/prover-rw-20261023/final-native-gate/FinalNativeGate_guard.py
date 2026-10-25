"""Sampled fixed-job RSS watchdog. No subprocesses, rlimits or VSize cap.

Not a continuous physical-memory theorem. Cgroup controls remain authoritative.
The one persistent thread exists before and throughout both collector snapshots.
"""
import os
import errno
import json
import resource
import signal
import threading
import time

BUDGET = 4 * 2**30
INTERVAL = 0.02
MAX_SAMPLES = 32768
MAX_LINEAGE = 256

class GuardError(RuntimeError):
    pass


def inherited_limits():
    return {name:list(resource.getrlimit(getattr(resource, name))) for name in
            sorted(dir(resource)) if name.startswith('RLIMIT_')}


def check_limits(limits, expected=None):
    if expected is not None and limits != expected:
        raise GuardError('inherited resource limits changed; no bypass')
    for name in ('RLIMIT_AS', 'RLIMIT_DATA'):
        if limits.get(name) != [resource.RLIM_INFINITY, resource.RLIM_INFINITY]:
            raise GuardError('unexpected inherited restriction: '+name)


class Gone(GuardError):
    """Only a specific ENOENT/ESRCH plus independent matching absence."""


class Proc:
    """Direct procfs; comm is descriptive, TGID/starttime form the envelope."""
    def __init__(self):
        self.events = []
        self.known = {}

    def record(self, operation, path, pid, tid, known, exc, evidence):
        row = dict(operation=operation, path=path, pid=pid, tid=tid,
                   known_stable_identity=known, errno=getattr(exc, 'errno', None),
                   error=repr(exc), independent_absence=evidence)
        self.events.append(row)
        if len(self.events) > MAX_SAMPLES:
            raise GuardError('proc event record limit')
        return json.dumps(row, sort_keys=True)

    def absent(self, path):
        try:
            os.stat(path)
        except FileNotFoundError as exc:
            if exc.errno == errno.ENOENT:
                return True
            raise
        return False

    def operation(self, operation, path, pid, tid, known, action, absence):
        try:
            return action()
        except (FileNotFoundError, ProcessLookupError) as exc:
            evidence = dict(path=absence, absent=None)
            try:
                evidence['absent'] = self.absent(absence)
            except Exception as check:
                evidence['error'] = repr(check)
            context = self.record(operation, path, pid, tid, known, exc, evidence)
            if exc.errno in (errno.ENOENT, errno.ESRCH) and evidence['absent'] is True:
                raise Gone(context) from exc
            raise GuardError(context) from exc
        except Exception as exc:
            # Context only: permission, malformed and unknown failures never mean gone.
            raise GuardError(self.record(operation, path, pid, tid, known, exc,
                                         dict(path=absence, absent=None))) from exc

    def read(self, path):
        with open(path) as stream:
            return stream.read()

    def identity_at(self, pid, tid=None):
        base = f'/proc/{pid}' if tid is None else f'/proc/{pid}/task/{tid}'
        expected = pid if tid is None else int(tid)
        key = (pid, tid)
        known = self.known.get(key)
        def get(name):
            return self.operation('read-'+name, base+'/'+name, pid, tid, known,
                                  lambda: self.read(base+'/'+name), base)
        def parse_stat(text):
            leader, tail = text.split(' (', 1)
            fields = tail.rsplit(') ', 1)[1].split()
            if int(leader) != expected or int(fields[19]) <= 0:
                raise ValueError('invalid stat identity')
            return fields
        def status(text):
            values = dict(line.split(':', 1) for line in text.splitlines() if ':' in line)
            if int(values['Tgid']) != pid or int(values['Pid']) != expected:
                raise ValueError('TGID/PID mismatch')
            return dict(tgid=int(values['Tgid']), pid=expected)
        try:
            first = parse_stat(get('stat')); before = status(get('status'))
            known = dict(**before, starttime=int(first[19]))
            if key in self.known and self.known[key] != known:
                raise ValueError('PID/task reuse before observation')
            if key not in self.known and len(self.known) >= MAX_SAMPLES:
                raise ValueError('proc identity record limit')
            self.known[key] = known
            after = status(get('status')); last = parse_stat(get('stat'))
            if after != before or int(last[19]) != known['starttime']:
                raise ValueError('PID/task reuse during observation')
            rss = int(last[21])*os.sysconf('SC_PAGE_SIZE')
            if rss < 0:
                raise ValueError('invalid RSS')
            return dict(pid=expected, tgid=pid, ppid=int(last[1]),
                        starttime=known['starttime'], rss_bytes=rss)
        except (Gone, GuardError):
            raise
        except Exception as exc:
            raise GuardError(self.record('parse-identity', base, pid, tid, known,
                                         exc, dict(path=base, absent=None))) from exc

    def identity(self, pid):
        return self.identity_at(pid)

    def optional(self, pid):
        try:
            return self.identity(pid)
        except Gone:
            return None
        except (FileNotFoundError, ProcessLookupError) as exc:
            # Preserve the original optional-boundary shape for custom proc readers.
            def fail():
                raise exc
            try:
                return self.operation('identity', f'/proc/{pid}', pid, None,
                    self.known.get((pid, None)), fail, f'/proc/{pid}')
            except Gone:
                return None

    def children(self, pid):
        before = self.identity(pid)
        base = f'/proc/{pid}/task'
        tids = self.operation('list-task', base, pid, None,
                              self.known.get((pid, None)), lambda: os.listdir(base), f'/proc/{pid}')
        result = set()
        for tid in tids:
            if not tid.isdecimal() or int(tid) <= 0:
                raise GuardError(self.record('parse-task-list', base, pid, tid,
                    self.known.get((pid, None)), ValueError('invalid task identity'),
                    dict(path=base, absent=None)))
            try:
                task = self.identity_at(pid, tid)
                path = base+'/'+tid+'/children'
                raw = self.operation('read-task-children', path, pid, tid,
                    self.known.get((pid, tid)), lambda: self.read(path), base+'/'+tid)
                after = self.identity_at(pid, tid)
                if (after['tgid'], after['starttime']) != (task['tgid'], task['starttime']):
                    raise GuardError('task identity changed')
            except Gone:
                # Parent envelope below must still close, or the error propagates.
                continue
            for child in raw.split():
                if not child.isdecimal() or int(child) <= 0:
                    raise GuardError(self.record('parse-task-children', path, pid, tid,
                        self.known.get((pid, tid)), ValueError('invalid child identity'),
                        dict(path=base+'/'+tid, absent=None)))
                result.add(int(child))
        after = self.identity(pid)
        if (after['tgid'], after['starttime']) != (before['tgid'], before['starttime']):
            raise GuardError('parent identity changed across task scan')
        return result

    def cancel(self, pid, starttime):
        # Stable handle before checks. Original cgroup remains authoritative.
        try:
            fd = self.operation('pidfd-open', f'/proc/{pid}', pid, None,
                dict(pid=pid, tgid=pid, starttime=starttime), lambda: os.pidfd_open(pid), f'/proc/{pid}')
        except Gone:
            return 'verified-disappeared'
        try:
            observed = self.optional(pid)
            if observed is None:
                return 'verified-disappeared'
            if observed['starttime'] != starttime:
                return 'reused-not-signalled'
            self.operation('pidfd-signal', f'/proc/{pid}', pid, None,
                self.known.get((pid, None)), lambda: signal.pidfd_send_signal(fd, signal.SIGKILL), f'/proc/{pid}')
            return 'verified-owned-signalled'
        finally:
            os.close(fd)


class Guard:
    budget = BUDGET
    max_samples = MAX_SAMPLES
    def __init__(self, proc=None, pid=None, notify=None):
        self.proc = proc or Proc()
        self.pid = os.getpid() if pid is None else pid
        self.notify = notify or (lambda: signal.raise_signal(signal.SIGUSR1))
        self.stop_event = threading.Event()
        self.ready = threading.Event()
        self.samples = []
        self.owned = {}
        self.lineage = []
        self.peak = 0
        self.error = None
        self.cancelled = []
        self.thread = None
        self.started = None
        self.stopped = None

    def remember(self, row, parent):
        pid = row['pid']
        if pid in self.owned:
            if self.owned[pid] != row['starttime']:
                raise GuardError('PID reuse: '+str(pid))
        else:
            if len(self.owned) >= MAX_LINEAGE:
                raise GuardError('lineage record limit')
            self.owned[pid] = row['starttime']
            self.lineage.append(dict(pid=pid, starttime=row['starttime'], parent=parent))

    def sample(self):
        live = {}
        pending = [(self.pid, None)] + [(p, 'retained-descendant') for p in self.owned if p != self.pid]
        while pending:
            pid, parent = pending.pop()
            if pid in live:
                continue
            row = self.proc.optional(pid)
            if row is None:
                if pid == self.pid:
                    raise GuardError('collector disappeared')
                continue
            if pid not in self.owned and parent is not None and row['ppid'] != parent:
                raise GuardError('unknown live-child lineage')
            self.remember(row, parent)
            live[pid] = row
            try:
                children = self.proc.children(pid)
            except Gone:
                if pid == self.pid:
                    raise GuardError('collector disappeared during task scan')
                # Keep the preceding RSS charge; never synthesize zero for this interval.
                children = set()
            pending.extend((child, pid) for child in children)
        total = sum(row['rss_bytes'] for row in live.values())
        self.peak = max(self.peak, total)
        if len(self.samples) >= self.max_samples:
            raise GuardError('sample record limit')
        self.samples.append(dict(monotonic=time.monotonic(),rss_bytes=total,
                                 processes=sorted(live),process_rss=live))
        if total > self.budget:
            raise GuardError('sampled aggregate job RSS exceeds fixed guard budget')

    def check(self):
        if self.error:
            raise GuardError(self.error)

    def cancel_owned(self):
        for pid, start in list(self.owned.items()):
            if pid == self.pid:
                continue
            try:
                outcome = self.proc.cancel(pid, start)
            except (OSError, ValueError, GuardError) as exc:
                outcome = 'cancellation-error: '+str(exc)
            self.cancelled.append(dict(pid=pid,starttime=start,outcome=outcome))

    def loop(self):
        try:
            while True:
                self.sample()
                self.ready.set()
                if self.stop_event.wait(INTERVAL):
                    self.sample()  # final observation before monitor exit
                    break
        except Exception as exc:
            self.error = type(exc).__name__+': '+str(exc)
            self.cancel_owned()
            self.ready.set()
            self.notify()

    def start(self):
        self.started = time.monotonic()
        self.thread = threading.Thread(target=self.loop, name='ResourceRssGOv3-resident-guard', daemon=True)
        self.thread.start()
        self.ready.wait(2)
        if not self.ready.is_set():
            raise GuardError('monitor failed to become ready')
        self.check()

    def finish(self, failed=False):
        self.stop_event.set()
        self.thread.join(2)
        if self.thread.is_alive():
            raise GuardError('monitor failed to stop')
        self.stopped = time.monotonic()
        if failed:
            self.cancel_owned()
        return dict(kind='sampled aggregate PROCESS RSS; TGID once; fixed job; not continuous',
                    budget_bytes=self.budget,interval_seconds=INTERVAL,max_samples=self.max_samples,
                    max_lineage=MAX_LINEAGE,peak_sampled_rss_bytes=self.peak,
                    samples=self.samples,lineage=self.lineage,error=self.error,
                    proc_events=getattr(self.proc, 'events', []),
                    cancellations=self.cancelled,started=self.started,stopped=self.stopped,
                    cgroup_peak='separate authoritative go-controls receipts; N/A if no scope')
