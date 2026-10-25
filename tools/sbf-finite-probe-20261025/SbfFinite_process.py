if __name__ == '__main__':
    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')
"""Actual read-only proc observations for the fixed future continuation.

No observation accepts a GO result. All APIs are local reads; tests replace
individual read APIs. Kernel proc exe links are intentional, not general paths.
"""
import os
import hashlib
from SbfFiniteLinux_capture import require, identity
from SbfFiniteLinux_backend import read_small
from SbfFinite_package import ENV, PACKAGE, UNIT, digest, pinned_file


def read(path, bound=65536):
    return read_small(path, bound=bound)


def executable(pid):
    fd = os.open('/proc/'+str(pid)+'/exe', os.O_RDONLY|os.O_CLOEXEC)
    try:
        s = os.fstat(fd)
        require(s.st_uid == 0 and s.st_gid == 0 and s.st_nlink == 1 and
                not s.st_mode & 0o022 and s.st_size <= 64*2**20, 'process executable rights')
        h, total = hashlib.sha256(), 0
        while True:
            raw = os.read(fd, 65536)
            if not raw:
                break
            total += len(raw)
            require(total <= s.st_size, 'process executable grew')
            h.update(raw)
        require(identity(s) == identity(os.fstat(fd)) and total == s.st_size,
                'process executable changed')
        return dict(sha256=h.hexdigest(), size=total)
    finally:
        os.close(fd)


def stat(pid):
    raw = read('/proc/'+str(pid)+'/stat').decode('ascii')
    leader, tail = raw.split(' (', 1)
    fields = tail.rsplit(') ', 1)[1].split()
    require(int(leader) == pid and len(fields) >= 22, 'actual proc stat identity')
    return dict(pid=pid, ppid=int(fields[1]), starttime=int(fields[19]))


def process(pid, role, expected):
    first = stat(pid)
    prefix = '/proc/'+str(pid)
    status = dict(line.split(':',1) for line in read(prefix+'/status').decode('ascii').splitlines())
    require(int(status['Tgid']) == int(status['Pid']) == pid and
            int(status['Threads']) >= 1, 'process TGID')
    envraw = read(prefix+'/environ')
    values = envraw.rstrip(b'\0').split(b'\0') if envraw else []
    require(all(b'=' in value for value in values), 'process environment syntax')
    env = dict(value.split(b'=',1) for value in values)
    require(len(env) == len(values), 'duplicate process environment')
    cmdline = read(prefix+'/cmdline')
    cgroup = read(prefix+'/cgroup').decode('ascii')
    require(cgroup.count('\n') == 1 and cgroup.startswith('0::/'), 'actual unified process scope')
    maps = read(prefix+'/maps', 2**20).decode('ascii').splitlines()
    mapped = set()
    kernel_maps = []
    for line in maps:
        parts = line.split(None,5)
        require(len(parts) >= 5, 'maps syntax')
        rights = parts[1]
        require(not ('w' in rights and 'x' in rights), 'writable executable map')
        if len(parts) == 6 and parts[5].startswith('/'):
            mapped.add(parts[5])
        elif 'x' in rights:
            require(len(parts) == 6 and parts[5] in ('[vdso]','[vsyscall]'),
                    'unapproved anonymous executable map')
            kernel_maps.append([parts[5],rights])
    require(mapped == set(expected['maps']), 'limited/changed runtime map')
    for path, item in expected['maps'].items():
        pinned_file(path, item['pin'], item['mode'])
    observed = dict(exe=executable(pid),
        uid=[int(x) for x in status['Uid'].split()],
        gid=[int(x) for x in status['Gid'].split()],
        groups=[int(x) for x in status['Groups'].split()],
        caps={k:int(status['Cap'+k],16) for k in ('Inh','Prm','Eff','Bnd','Amb')},
        threads=int(status['Threads']), nnp=int(status['NoNewPrivs']),
        seccomp=int(status['Seccomp']), env=digest(envraw), cmdline=digest(cmdline),
        limits=digest(read(prefix+'/limits')), maps=expected['maps'],kernel_maps=sorted(kernel_maps))
    require(set(expected) == set(observed) and observed == expected, 'role source/runtime/env/limits/control pin')
    require(stat(pid) == first and first['starttime'] > 0, 'process ancestry/start drift')
    return dict(first, role=role, cgroup=cgroup, observation=observed)


def lineage(approved):
    """Read helper -> sudo [monitor] -> collector, never trust supplied PIDs.

    Whether sudo inserts a monitor is detected from live executable identity.
    Role metadata must pin the specific installed sudo behavior and all IDs,
    including real IDs; no assumption that sudo has three root IDs.
    """
    roles = approved['roles']
    require(set(roles) == {'collector','sudo','sudo-monitor','helper'}, 'all route pins')
    helper = process(os.getpid(), 'helper', roles['helper'])
    parent = stat(helper['ppid'])
    # A monitor is another instance of the pinned sudo executable. Its own
    # parent must also be sudo; otherwise the one-sudo route is required.
    grand = stat(parent['ppid'])
    monitor = executable(grand['pid']) == roles['sudo']['exe']
    if monitor:
        middle = [process(grand['pid'], 'sudo', roles['sudo']),
                  process(parent['pid'], 'sudo-monitor', roles['sudo-monitor'])]
    else:
        middle = [process(parent['pid'], 'sudo', roles['sudo'])]
    collector = process(middle[0]['ppid'], 'collector', roles['collector'])
    rows = [collector]+middle+[helper]
    require(len({r['pid'] for r in rows}) == len(rows), 'lineage cycle')
    for index, row in enumerate(rows):
        require(row['cgroup'] == '0::'+approved['scope_path']+'\n', 'process scope escape')
        if index:
            require(row['ppid'] == rows[index-1]['pid'], 'broken live ancestry')
    return rows
