from pathlib import Path
p=Path('tools/prover-rw-20261023/final-native-gate/FinalNativeGate_guard.py')
s=p.read_text().replace('import os\n','import os\nimport errno\nimport json\n',1)
a=s.index('class Proc:');b=s.index('\n\nclass Guard:',a)
s=s[:a]+'''class Gone(GuardError):
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
''' + s[b:]
s=s.replace("except FileNotFoundError:\n                if self.proc.optional(pid) is not None:\n                    raise GuardError('unknown live-child visibility')\n                children = set()", "except Gone:\n                if pid == self.pid:\n                    raise GuardError('collector disappeared during task scan')\n                # Keep the preceding RSS charge; never synthesize zero for this interval.\n                children = set()")
s=s.replace('cancellations=self.cancelled,started=',"proc_events=getattr(self.proc, 'events', []),\n                    cancellations=self.cancelled,started=")
p.write_text(s)
