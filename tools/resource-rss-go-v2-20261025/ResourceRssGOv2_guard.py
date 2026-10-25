"""Sampled metadata-only RSS watchdog. No subprocesses, rlimits or VSize cap.

Not a continuous physical-memory theorem. Cgroup controls remain authoritative.
The one persistent thread exists before and throughout both collector snapshots.
"""
import os
import resource
import signal
import threading
import time

BUDGET = 512 * 2**20
INTERVAL = 0.02
MAX_SAMPLES = 8192
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


class Proc:
    """Direct procfs only; status TGID and stat identity/RSS, never thread sum."""
    def read(self, path):
        with open(path) as stream:
            return stream.read()

    def identity(self, pid):
        text = self.read(f'/proc/{pid}/stat')
        leader, tail = text.split(' (', 1)
        fields = tail.rsplit(') ', 1)[1].split()
        status = dict(line.split(':', 1) for line in self.read(f'/proc/{pid}/status').splitlines() if ':' in line)
        if int(leader) != pid or int(status['Tgid']) != pid or int(status['Pid']) != pid:
            raise GuardError('unknown non-TGID identity')
        # stat field22=starttime,23=vsize,24=rss; state starts field3.
        result = dict(pid=pid, ppid=int(fields[1]), starttime=int(fields[19]),
                      rss_bytes=int(fields[21])*os.sysconf('SC_PAGE_SIZE'))
        again = self.read(f'/proc/{pid}/stat').rsplit(') ', 1)[1].split()
        if int(again[19]) != result['starttime']:
            raise GuardError('PID reuse during proc observation')
        if result['rss_bytes'] < 0 or result['starttime'] <= 0:
            raise GuardError('invalid proc identity/RSS')
        return result

    def absent(self, path):
        try:
            os.stat(path)
        except FileNotFoundError:
            return True
        return False

    def optional(self, pid):
        try:
            return self.identity(pid)
        except FileNotFoundError:
            if self.absent(f'/proc/{pid}'):
                return None
            raise GuardError('unknown live-child visibility')

    def children(self, pid):
        result = set()
        for tid in os.listdir(f'/proc/{pid}/task'):
            if not tid.isdecimal():
                raise GuardError('invalid task identity')
            try:
                raw = self.read(f'/proc/{pid}/task/{tid}/children')
            except FileNotFoundError:
                if self.absent(f'/proc/{pid}/task/{tid}'):
                    continue
                raise GuardError('unknown live task children')
            for child in raw.split():
                if not child.isdecimal() or int(child) <= 0:
                    raise GuardError('invalid child identity')
                result.add(int(child))
        return result

    def cancel(self, pid, starttime):
        # Open the stable handle BEFORE rechecking identity; reuse never signalled.
        try:
            fd = os.pidfd_open(pid)
        except ProcessLookupError:
            return 'disappeared'
        try:
            observed = self.optional(pid)
            if observed is None:
                return 'disappeared'
            if observed['starttime'] != starttime:
                return 'reused-not-signalled'
            signal.pidfd_send_signal(fd, signal.SIGKILL)
            return 'verified-owned-signalled'
        finally:
            os.close(fd)


class Guard:
    def __init__(self, proc=None, pid=None, notify=None):
        self.proc = proc or Proc()
        self.pid = os.getpid() if pid is None else pid
        self.notify = notify or (lambda: os.kill(self.pid, signal.SIGUSR1))
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
            except FileNotFoundError:
                if self.proc.optional(pid) is not None:
                    raise GuardError('unknown live-child visibility')
                children = set()
            pending.extend((child, pid) for child in children)
        total = sum(row['rss_bytes'] for row in live.values())
        self.peak = max(self.peak, total)
        if len(self.samples) >= MAX_SAMPLES:
            raise GuardError('sample record limit')
        self.samples.append(dict(monotonic=time.monotonic(),rss_bytes=total,
                                 processes=sorted(live),process_rss=live))
        if total > BUDGET:
            raise GuardError('sampled aggregate metadata RSS exceeds 512MiB')

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
        self.thread = threading.Thread(target=self.loop, name='ResourceRssGOv2-resident-guard', daemon=True)
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
        return dict(kind='sampled aggregate PROCESS RSS; TGID once; metadata only; not continuous',
                    budget_bytes=BUDGET,interval_seconds=INTERVAL,max_samples=MAX_SAMPLES,
                    max_lineage=MAX_LINEAGE,peak_sampled_rss_bytes=self.peak,
                    samples=self.samples,lineage=self.lineage,error=self.error,
                    cancellations=self.cancelled,started=self.started,stopped=self.stopped,
                    cgroup_peak='separate authoritative go-controls receipts; N/A if no scope')
