if __name__ == '__main__':
    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')
"""Concrete UNEXECUTED fixed tiny guest backend. No usable privileged CLI.

Internal functions require a future independently authorized single-threaded
root helper. These APIs do not establish producer freshness or runtime closure.
The only entrypoint below always denies, before native library loading.
"""
import errno
import fcntl
import json
import os
import stat
import time
import select
import signal
from SbfFiniteLinux_capture import (PublicOutput, Denied, require, ROOT, OWN,
    ENV, PROBE, DIR_FLAGS, FILE_FLAGS, check_dir, check_entry, inode,
    open_safe_ancestry, create_fixed_layout, validate_manifest,
    FD_AUDIT_TEXT)
from SbfFiniteLinux_abi import (LinuxABI, I, U, C, NEWNS, NEWNET, NEWPID, PRIVATE,
    RDONLY, NOSUID, NODEV, NOEXEC)

# No complete finite loader/import/proc/resource closure has been supplied.
DEADLINE = 5.0


def read_small(path, api=os, bound=65536, directory=None):
    fd = api.open(path, FILE_FLAGS, dir_fd=directory)
    try:
        chunks, total = [], 0
        while True:
            raw = api.read(fd, min(4096,bound+1-total))
            if not raw:
                break
            total += len(raw)
            require(total <= bound, 'metadata bound')
            chunks.append(raw)
        return b''.join(chunks)
    finally:
        api.close(fd)


def status(api=os):
    raw = read_small('/proc/self/status', api).decode('ascii')
    rows = [line.split(':',1) for line in raw.splitlines()]
    require(all(len(r) == 2 for r in rows), 'status syntax')
    require(len({r[0] for r in rows}) == len(rows), 'status duplicate')
    return {k:v.strip() for k,v in rows}


def namespaces(api=os):
    # Following these fixed kernel namespace magic links is intentional; never
    # a mount path or /proc/self/fd fallback. fstat identity, not caller strings.
    result = {}
    for name in ('mnt','net','pid','user'):
        fd = api.open('/proc/self/ns/'+name, api.O_RDONLY | api.O_CLOEXEC)
        try:
            result[name] = inode(api.fstat(fd))
        finally:
            api.close(fd)
    return result


def inventory(api=os):
    names = api.listdir('/proc/self/fd')
    require(len(names) <= 4096, 'FD inventory bound')
    living = []
    for name in names:
        require(name.isascii() and name.isdigit(), 'FD syntax')
        fd = int(name)
        try:
            api.fstat(fd)
        except OSError as e:
            require(e.errno == errno.EBADF, 'FD inspection failure')
        else:
            living.append(fd)
    return sorted(living)


def mount_table(api=os):
    raw = read_small('/proc/self/mountinfo', api, 1024*1024).decode('ascii')
    result = {}
    for line in raw.splitlines():
        fields = line.split()
        require('-' in fields and fields.index('-') >= 6, 'mountinfo syntax')
        sep = fields.index('-')
        require(len(fields) == sep+4, 'mountinfo fields')
        mid = int(fields[0])
        require(mid > 0 and mid not in result, 'mount ID')
        require(not any(f.startswith(('shared:','master:','propagate_from:'))
                        for f in fields[6:sep]), 'nonprivate mount')
        result[mid] = dict(parent=int(fields[1]), path=fields[4],
                           options=set(fields[5].split(',')), fs=fields[sep+1])
    require(result, 'empty mount table')
    return result


def verify_mount(fd, abi, required, api=os, fs=None):
    mid = abi.mount_id(fd)
    rows = mount_table(api)
    require(mid in rows and required <= rows[mid]['options'], 'mount flags/ID')
    if fs is not None:
        require(rows[mid]['fs'] == fs, 'filesystem type')
    return mid


def child_namespaces(before, api=os):
    require(api.getpid() == 1, 'guest must be PID1')
    current = namespaces(api)
    require(all(current[n] != before[n] for n in ('mnt','net','pid')) and
            current['user'] == before['user'], 'actual namespace transition')
    require(status(api)['Threads'] == '1', 'single threaded guest')
    return current


def root_helper_preflight(api=os):
    require(api.getresuid() == api.getresgid() == (0,0,0), 'root helper IDs')
    s = status(api)
    require(s['Threads'] == '1', 'root helper must be single threaded')
    require(s['NoNewPrivs'] == '0' and s['Seccomp'] == '0', 'unexpected helper control state')
    needed = sum(1<<n for n in (5,6,7,8,18,21))
    require(int(s['CapEff'],16) & needed == needed, 'helper setup/cancellation capabilities')
    last = read_small('/proc/sys/kernel/cap_last_cap',api,16)
    require(last == b'40\n', 'pinned capability ABI')
    cg = read_small('/proc/self/cgroup',api,4096)
    require(cg.startswith(b'0::/') and cg.count(b'\n') == 1, 'unified cgroup')
    # Concrete finite continuation separately rechecks current role lineage,
    # package pins and full resource admission; this preflight is not authority.
    return namespaces(api), cg, 40


def validate_runtime(manifest):
    from SbfFinite_validate import validate
    return validate({'schema':'SbfFinite-runtime-v1','runtime':manifest})


def capture_runtime(rootfd,manifest):
    """Read-only verification of installed exclusive copies; no recopy/adoption."""
    validate_runtime(manifest)
    from SbfFinite_package import verify_tree
    verify_tree(rootfd)


def fixed_backend_body():
    # No full Producer approval premise. Concrete root continuation alone calls
    # this after separate finite operational pins, fresh admission and lineage.
    from SbfFinite_fixed import RUNTIME
    manifest = RUNTIME
    validate_runtime(manifest)
    abi = LinuxABI()
    parent = os.getppid()
    parentfd = abi.call('pidfd_open',I(parent),U(0))
    own = root = outputs = nullfd = None
    output = None
    previous = {}
    def terminate(*_):
        raise Denied('helper parent/termination event; retain capture')
    try:
        require(parentfd >= 3, 'helper parent pidfd alias')
        for sig in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP):
            previous[sig] = signal.getsignal(sig)
            signal.signal(sig,terminate)
        require(abi.prctl(1,15) == 0, 'helper parent-death arm')
        require(os.getppid() == parent, 'helper parent changed during arm')
        parent_alive(parentfd)
        os.close(parentfd); parentfd = None
        own,root,outputs = create_fixed_layout()
        output = PublicOutput(outputs,0)
        nullfd = fixed_null()
        result = internal_backend(root,output,nullfd,abi,manifest=manifest)
        from SbfFinite_package import journal
        journal('root-result.json',dict(kind='finite observation ONLY',public=result))
        return 0
    finally:
        if output is not None: output.close()
        for fd in (parentfd,nullfd,outputs,root,own):
            if fd is not None: os.close(fd)
        for sig,handler in previous.items(): signal.signal(sig,handler)


def fixed_null(api=os):
    parent = open_safe_ancestry('/dev') if api is os else api.safe_dev()
    try:
        fd = api.open('null', FILE_FLAGS, dir_fd=parent)
        try:
            s = api.fstat(fd)
            require(stat.S_ISCHR(s.st_mode) and s.st_uid == 0 and
                    (api.major(s.st_rdev),api.minor(s.st_rdev)) == (1,3), 'null device')
            require(fcntl.fcntl(fd,fcntl.F_GETFL) & os.O_ACCMODE == os.O_RDONLY,
                    'readonly stdin') if api is os else api.readonly_null(fd)
            return fd
        except BaseException:
            api.close(fd)
            raise
    finally:
        api.close(parent)


def subdirectory(rootfd, name, api=os):
    require(name in ('tmp','proc','dev'), 'fixed target')
    fd = api.open(name, DIR_FLAGS, dir_fd=rootfd)
    try:
        s = api.fstat(fd)
        require(stat.S_ISDIR(s.st_mode) and s.st_uid == 0 and
                not s.st_mode & 0o022, 'target owner/type')
        require(not api.listdir(fd), 'mount targets must be empty')
        return fd
    except BaseException:
        api.close(fd)
        raise


def private_propagation(abi,api=os):
    hostroot = api.open('/', DIR_FLAGS)
    try:
        abi.attr(hostroot, propagation=PRIVATE, recursive=True)
        mount_table(api)  # deny any remaining shared/master propagation
    finally:
        api.close(hostroot)


def mount_guest(rootfd, abi, api=os):
    """Use only NEW mount object fd for subtargets and eventual chroot.

    mount_setattr propagation applies to namespace / in private_propagation before capture/open_tree/fsopen.
    open_tree is NONrecursive; source must have no submounts (checked below).
    move_mount targets are descriptor-only. Retained tree fd refers to attached
    clone, never the old covered directory. No name reopen or /proc/fd magic.
    """
    old_id = abi.mount_id(rootfd)
    table = mount_table(api)
    require(not any(r['path'].startswith(ROOT+'/') for r in table.values()),
            'source contains submounts')
    newroot = abi.tree(rootfd)
    try:
        require(abi.mount_id(newroot) != old_id, 'clone mount identity')
        abi.attr(newroot, RDONLY | NOSUID | NODEV)
        abi.attach(newroot,rootfd)
        require(abi.mount_id(newroot) != old_id, 'retained new mount required')
        root_id = verify_mount(newroot,abi,{'ro','nosuid','nodev'},api)
        mount_ids = {'root':root_id}
        for name, kind in (('tmp','tmpfs'),('proc','proc')):
            target = subdirectory(newroot,name,api)
            mounted = None
            try:
                require(abi.mount_id(target) == root_id, 'target outside NEW root mount')
                mounted = abi.filesystem(kind,api.close)
                abi.attach(mounted,target)
                flags = {'nosuid','nodev','noexec', 'ro' if kind == 'proc' else 'rw'}
                mid = verify_mount(mounted,abi,flags,api,kind)
                require(mid != root_id and mid not in mount_ids.values(), 'submount identity')
                mount_ids[name] = mid
                if name == 'tmp':
                    s = api.fstat(mounted)
                    require(s.st_uid == 0 and stat.S_IMODE(s.st_mode) == 0o1777,
                            'finite writable tmp ownership/mode')
            finally:
                if mounted is not None:
                    api.close(mounted)
                api.close(target)
        dev = subdirectory(newroot,'dev',api)
        api.close(dev)  # empty sealed directory, no device binds, NODEV retained
        table = mount_table(api)
        under = {mid:r for mid,r in table.items()
                 if r['path'] == ROOT or r['path'].startswith(ROOT+'/')}
        require(set(under) == set(mount_ids.values()), 'unexpected guest submount')
        require(under[mount_ids['tmp']]['parent'] == root_id and
                under[mount_ids['proc']]['parent'] == root_id, 'submount topology')
        return newroot, mount_ids
    except BaseException:
        api.close(newroot)
        raise


def private_proc_check(expected_ns, api=os):
    require(api.getpid() == 1, 'private proc PID1')
    # Actual proc namespace objects for visible PID1 and self must equal the
    # pre-chroot guest namespace inode. Not matching caller-provided strings.
    for path in ('/proc/1/ns/pid','/proc/self/ns/pid'):
        fd = api.open(path, api.O_RDONLY | api.O_CLOEXEC)
        try:
            require(inode(api.fstat(fd)) == expected_ns['pid'], 'proc PID namespace association')
        finally:
            api.close(fd)
    require(namespaces(api) == expected_ns, 'namespace drift')


def stdio_install(output, nullfd, api=os):
    require(set(output.rows) == {'stdout','stderr'}, 'fixed output handles')
    require(nullfd > 2 and all(row['w'] > 2 for row in output.rows.values()),
            'nonoverlapping stdio sources')
    for name in ('stdout','stderr'):
        output.verify(name)
    api.dup2(nullfd,0,inheritable=True)
    api.dup2(output.rows['stdout']['w'],1,inheritable=True)
    api.dup2(output.rows['stderr']['w'],2,inheritable=True)
    return {fd:inode(api.fstat(fd)) for fd in (0,1,2)}


def stdio_check(expected, api=os):
    require(inventory(api) == [0,1,2], 'living escape/control/socket/root/output FD')
    for fd in (0,1,2):
        require(inode(api.fstat(fd)) == expected[fd], 'stdio inode changed')
    s = api.fstat(0)
    require(stat.S_ISCHR(s.st_mode) and (api.major(s.st_rdev),api.minor(s.st_rdev)) == (1,3),
            'stdin null identity')
    for fd in (1,2):
        s = api.fstat(fd)
        require(stat.S_ISREG(s.st_mode) and s.st_uid == 0 and s.st_nlink == 1 and
                stat.S_IMODE(s.st_mode) == 0o600, 'root-owned output writers')
    if api is os:
        require(fcntl.fcntl(0,fcntl.F_GETFL) & os.O_ACCMODE == os.O_RDONLY,
                'stdin access')
        for fd in (1,2):
            require(fcntl.fcntl(fd,fcntl.F_GETFL) & os.O_ACCMODE == os.O_WRONLY,
                    'output access')


def dropped_check(expected_ns,cgroup,root_inode,stdio,abi,api=os):
    require(api.getresuid() == api.getresgid() == (1000,1000,1000) and
            api.getgroups() == [], 'all saved IDs/groups')
    s = status(api)
    require(all(int(s[k],16) == 0 for k in
                ('CapInh','CapPrm','CapEff','CapBnd','CapAmb')) and
            s['NoNewPrivs'] == '1' and s['Threads'] == '1', 'drop control verification')
    require(abi.prctl(39) == 1, 'NNP actual query')
    require(read_small('/proc/self/cgroup',api,4096) == cgroup, 'cgroup drift')
    require(inode(api.stat('/')) == root_inode and
            inode(api.stat('.')) == root_inode, 'chroot/cwd inode')
    private_proc_check(expected_ns,api)
    stdio_check(stdio,api)


# Captured postexec body/argv/env are byte-identical, including SbfSeal label.
from SbfFinite_fixed import ARGV as FIXED_PROBE


def guest(rootfd,output,nullfd,before,cgroup,last_cap,abi,api=os,manifest=None,parentfd=None):
    """Child-only branch. Every exception exits, never host fallback exec."""
    try:
        require(parentfd is not None, 'owned helper pidfd required')
        require(abi.prctl(1,9) == 0, 'guest parent-death arm')
        parent_alive(parentfd)
        ns = child_namespaces(before,api)
        private_propagation(abi,api)
        capture_runtime(rootfd,manifest)
        newroot, mount_ids = mount_guest(rootfd,abi,api)
        try:
            root_inode = inode(api.fstat(newroot))
            stdio = stdio_install(output,nullfd,api)
            api.fchdir(newroot)
            api.chroot('.')  # fixed dot relative to NEW mount root, never path input
            api.chdir('/')
            require(abi.mount_id(newroot) == mount_ids['root'], 'chroot mount ID')
            private_proc_check(ns,api)
        finally:
            api.close(newroot)
        # Closes inherited parent readfds, pidfds, capture directory fds, host
        # root, stdin source, stdout/stderr sources and arbitrary high/socket fds.
        # Retain only the owned parent liveness handle through credential drop.
        # dup2 is before close_range; old roots/readers/writers cannot survive.
        api.dup2(parentfd,3,inheritable=False)
        abi.zero('close_range',U(4),U(0xffffffff),U(0))
        require(inventory(api) == [0,1,2,3], 'pending descriptor after root closure')
        abi.guest_limits()  # never reduce NOFILE while high inherited fds live
        abi.drop(last_cap)
        # setresuid/setresgid may clear PDEATHSIG: rearm, then stable-handle
        # check catches parent death in that gap before any guest exec.
        require(abi.prctl(1,9) == 0, 'guest parent-death rearm')
        parent_alive(3)
        api.close(3)
        dropped_check(ns,cgroup,root_inode,stdio,abi,api)
        api.execve(FIXED_PROBE[0],FIXED_PROBE,dict(ENV))
        raise Denied('exec unexpectedly returned')
    except BaseException:
        # No privileged diagnostic export of paths or exception data.
        try:
            abi.close_escape_fds()
        finally:
            api._exit(126)


def pidfd_identity(fd,pid,api=os):
    # Fixed actual fdinfo, not caller evidence; own direct-child pidfd retained until
    # wait. No inherited arbitrary fd is accepted by the lifecycle below.
    raw = read_small('/proc/self/fdinfo/'+str(fd),api,4096).decode('ascii')
    rows = dict(line.split(':',1) for line in raw.splitlines() if ':' in line)
    require(int(rows['Pid']) == pid, 'pidfd actual host PID')


def owned_wait(pid,pidfd,abi,api=os,clock=time):
    """Wait only direct own child. Timeout cancellation uses retained pidfd.

    No SIGCHLD handler/other reaper permitted. Never send signals by numeric PID.
    Parent is outside the guest PID namespace; pid is the host-visible clone PID.
    Reap after cancellation (even timeout) before returning/raising. Kernel wait
    after SIGKILL can await D-state completion; no false bounded-exit guarantee.
    """
    deadline = clock.monotonic()+DEADLINE
    while clock.monotonic() < deadline:
        waited, result = api.waitpid(pid,api.WNOHANG)
        require(waited in (0,pid), 'unexpected wait identity')
        if waited == pid:
            return waited,result
        clock.sleep(0.01)
    abi.kill_owned(pidfd)
    while True:
        try:
            waited,result = api.waitpid(pid,0)
            require(waited == pid, 'cancelled child wait identity')
            break
        except InterruptedError:
            continue
    raise Denied('deadline; own child killed and reaped; no output')


def internal_backend(rootfd,output,nullfd,abi,api=os,clock=time,manifest=None):
    """Future helper continuation, deliberately no CLI/admission connection.

    Must run only once in a disposable independently scoped root helper. Parent
    after unshare NEWPID remains host PIDns. CPython os.fork creates guest PID1,
    then parent opens its pidfd while the direct child remains unreaped/gated.
    No additional thread/reaper/monitor is created here.
    """
    before,cgroup,last_cap = root_helper_preflight(api)
    # Require normal SIGCHLD disposition, so unreaped child cannot disappear.
    if api is os:
        import signal
        import threading
        require(threading.current_thread() is threading.main_thread(), 'main thread only')
        require(signal.getsignal(signal.SIGCHLD) == signal.SIG_DFL, 'external reaper')
    selfpidfd = abi.call('pidfd_open',I(api.getpid()),U(0))
    require(selfpidfd >= 3, 'helper pidfd alias')
    try:
        gate_r,gate_w = api.pipe2(0x80000)
    except BaseException:
        api.close(selfpidfd)
        raise
    try:
        abi.zero('unshare',C.c_ulong(NEWNS | NEWNET | NEWPID))
        pid = api.fork()
    except BaseException:
        api.close(gate_r);api.close(gate_w)
        api.close(selfpidfd)
        raise
    if pid == 0:
        try:
            api.close(gate_w)
            token = api.read(gate_r,2)
            api.close(gate_r)
            require(token == b'G', 'parent lifecycle gate closed')
            guest(rootfd,output,nullfd,before,cgroup,last_cap,abi,api,manifest,selfpidfd)
        except BaseException:
            try:
                abi.close_escape_fds()
            finally:
                api._exit(126)
        api._exit(126)
    reaped = False
    pidfd = None
    try:
        api.close(gate_r)
        require(type(pid) is int and pid > 1, 'actual direct child host PID')
        # No reaper or other thread: an unreaped direct child cannot have its
        # PID reused, including if it exits before pidfd_open. It cannot exec
        # before this parent releases the gate. CPython performs native hooks.
        pidfd = abi.call('pidfd_open',I(pid),U(0))
        require(pidfd >= 3, 'own pidfd must not alias stdio')
        pidfd_identity(pidfd,pid,api)
        abi.check_owned_signal(pidfd)
        output.close_writers()
        require(api.write(gate_w,b'G') == 1, 'parent lifecycle gate write')
        api.close(gate_w)
        gate_w = None
        waited,result = owned_wait(pid,pidfd,abi,api,clock)
        reaped = True
        return output.collect(waited,pid,result)
    except BaseException:
        if not reaped:
            # Before pidfd acquisition the child is still blocked on gate EOF,
            # so failure closes the gate and reaps WITHOUT numeric-PID signalling.
            if gate_w is not None:
                api.close(gate_w)
                gate_w = None
            if pidfd is not None:
                try:
                    abi.kill_owned(pidfd)
                except OSError as error:
                    if error.errno != errno.ESRCH:
                        raise
            try:
                while True:
                    try:
                        got,_ = api.waitpid(pid,0)
                        require(got == pid, 'cleanup wait identity')
                        break
                    except InterruptedError:
                        continue
            except ChildProcessError:
                # owned_wait already reaped a timeout child before denying.
                pass
        raise
    finally:
        if gate_w is not None:
            api.close(gate_w)
        if pidfd is not None:
            api.close(pidfd)
        api.close(selfpidfd)


def parent_alive(fd):
    poller = select.poll()
    poller.register(fd, select.POLLIN | select.POLLHUP | select.POLLERR)
    require(poller.poll(0) == [], 'owned parent exited/handle error')
