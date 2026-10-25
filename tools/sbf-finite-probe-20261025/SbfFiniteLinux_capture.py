if __name__ == '__main__':
    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')
"""Finite source-only replacement for SbfClosure_setup; no privileged entrypoint.

Filesystem primitives run in ordinary temporary directories in local tests only.
They are NOT authorization for root use. No ctypes, mount, fork, exec or shell.
"""
import errno
import hashlib
import json
import os
import stat
import time

class Denied(RuntimeError):
    pass


def require(condition, reason):
    if not condition:
        raise Denied(reason)


def digest(raw):
    return dict(sha256=hashlib.sha256(raw).hexdigest(), size=len(raw))


def canonical(raw):
    require(type(raw) is str and raw.startswith('/') and raw != '/', 'absolute file path')
    components = raw[1:].split('/')
    require(all(part not in ('', '.', '..') and '\x00' not in part
                and part.isascii() and all(32 < ord(c) < 127 for c in part)
                for part in components), 'unsafe path component')
    return components


def component(name):
    require(type(name) is str and canonical('/'+name) == [name], 'single component')
    return name


DIR_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
FILE_FLAGS = os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK
OWN = '/var/lib/SbfFinite-20261025-v1'
ROOT = OWN+'/rootfs'
UID = GID = 1000
MAX_FILE = 16*2**20
MAX_TOTAL = 64*2**20
OUTPUT_BOUND = 16384
ENV = {'PATH': '/usr/bin', 'LC_ALL': 'C', 'HOME': '/probe', 'TMPDIR': '/tmp'}
# Exact same audit text is embedded in the fixed postexec probe and exercised
# with mock OS metadata locally. listdir closes its inspection fd before fstat;
# EBADF identifies CLOSED inspection entries, never permits a surviving fd3.
# Requires single-threaded probe and correctly mounted private proc. No bound
# based on RLIMIT_NOFILE: inherited high descriptors survive lowering that limit.
from SbfFinite_fixed import OWN, ROOT, ENV, ARGV
PROBE = ARGV
FD_AUDIT_TEXT = ARGV[-1][ARGV[-1].index('def SbfSeal_fds'):ARGV[-1].index('assert os.getresuid')]


def identity(s):
    return (s.st_dev, s.st_ino, s.st_mode, s.st_uid, s.st_gid, s.st_nlink,
            s.st_size, s.st_mtime_ns, s.st_ctime_ns)


def inode(s):
    return (s.st_dev, s.st_ino)


def check_dir(fd, owner):
    s = os.fstat(fd)
    require(stat.S_ISDIR(s.st_mode) and s.st_uid == s.st_gid == owner, 'directory owner/type')
    require(not s.st_mode & 0o022, 'writable ancestry')
    return s


def check_entry(parent, name, fd):
    # Supplemental identity check; security comes from dirfd + immutable ancestry,
    # NOT from this comparison preventing a subsequent attacker rename.
    require(inode(os.stat(component(name), dir_fd=parent, follow_symlinks=False))
            == inode(os.fstat(fd)), 'entry replaced')


def open_safe_ancestry(path):
    """Root-only non-writable ancestry; no sticky or user-owned ancestor fallback.

    Every open is component-relative. No writes until ALL ancestry checked.
    A root adversary is outside the proposed boundary; no same-uid writer allowed.
    """
    parts = canonical(path)
    fd = os.open('/', DIR_FLAGS)
    try:
        check_dir(fd, 0)
        for name in parts:
            child = os.open(name, DIR_FLAGS, dir_fd=fd)
            try:
                check_dir(child, 0)
                check_entry(fd, name, child)
            except BaseException:
                os.close(child)
                raise
            os.close(fd)
            fd = child
        return fd
    except BaseException:
        os.close(fd)
        raise


def exclusive_dir(parent, name, owner):
    """Parent must already be pinned and non-writable to the adversary.

    mkdir+open is safe under that premise, not under an attacker-owned parent.
    No exist_ok, chmod/chown-by-name, or reopening an unchecked path.
    """
    check_dir(parent, owner)
    name = component(name)
    os.mkdir(name, 0o700, dir_fd=parent)
    fd = os.open(name, DIR_FLAGS, dir_fd=parent)
    try:
        check_dir(fd, owner)
        check_entry(parent, name, fd)
        require(stat.S_IMODE(os.fstat(fd).st_mode) == 0o700, 'exclusive directory mode')
        return fd
    except BaseException:
        os.close(fd)
        raise


def create_fixed_layout():
    """Open installed fixed root; outputs exclusively created by PublicOutput.

    Installer already made own/rootfs/public-output; exact setup tree is verified
    separately. No existing arbitrary tree is adopted. One shot stdout/stderr.
    """
    require(os.getresuid() == os.getresgid() == (0,0,0), 'root IDs')
    own = root = outputs = None
    try:
        own = open_safe_ancestry(OWN)
        root = open_safe_ancestry(ROOT)
        outputs = open_safe_ancestry(OWN+'/public-output')
        require(not os.listdir(outputs), 'fresh output directory')
        return own,root,outputs
    except BaseException:
        for fd in (outputs,root,own):
            if fd is not None: os.close(fd)
        raise


class PublicOutput:
    """Fixed files only. Root parent retains read handles, never exports paths.

    Child receives dup2 writers as 1/2 before dropping IDs; file permissions stay
    0600 root, so guest cannot reopen or replace. Parent closes its writers before
    wait, child RLIMIT_FSIZE=16KiB, waits for exact own child, then collects bounded
    public format. No user-owned output destination or arbitrary root reader.
    """
    def __init__(self, directory, owner):
        check_dir(directory, owner)
        self.parent = os.dup(directory)
        self.owner = owner
        self.rows = {}
        try:
            for name in ('stdout','stderr'):
                w = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL |
                            os.O_NOFOLLOW | os.O_CLOEXEC, 0o600, dir_fd=self.parent)
                self.rows[name] = dict(w=w, r=None, inode=inode(os.fstat(w)))
                r = os.open(name, FILE_FLAGS, dir_fd=self.parent)
                self.rows[name]['r'] = r
                require(inode(os.fstat(r)) == self.rows[name]['inode'], 'output identity')
                self.verify(name)
        except BaseException:
            self.close()
            raise

    def verify(self, name):
        row = self.rows[name]
        s = os.fstat(row['r'])
        require(stat.S_ISREG(s.st_mode) and s.st_uid == self.owner and s.st_nlink == 1
                and stat.S_IMODE(s.st_mode) == 0o600, 'output rights/type')
        require(inode(s) == row['inode'] and s.st_size <= OUTPUT_BOUND, 'output inode/size')
        check_entry(self.parent, name, row['r'])

    def close_writers(self):
        for row in self.rows.values():
            if row['w'] is not None:
                os.close(row['w'])
                row['w'] = None

    def collect(self, waited_pid, expected_pid, wait_status):
        # These arguments must originate from actual waitpid, not caller claims;
        # this object alone is not an authorization or live parent implementation.
        require(type(expected_pid) is int and expected_pid > 1 and waited_pid == expected_pid,
                'wrong wait identity')
        require(os.WIFEXITED(wait_status) and os.WEXITSTATUS(wait_status) == 0, 'child failed')
        require(all(r['w'] is None for r in self.rows.values()), 'parent writer still open')
        result = {}
        for name, row in self.rows.items():
            self.verify(name)
            before = identity(os.fstat(row['r']))
            os.lseek(row['r'], 0, os.SEEK_SET)
            raw = os.read(row['r'], OUTPUT_BOUND+1)
            require(len(raw) <= OUTPUT_BOUND, 'output overflow')
            require(before == identity(os.fstat(row['r'])), 'output changed while collecting')
            result[name] = raw
        require(result['stderr'] == b'', 'probe stderr')
        expected = (json.dumps({'SbfSeal':'tiny-public-v1', 'uid':1000,
                               'gid':1000, 'fds':[0,1,2]}, sort_keys=True)+'\n').encode()
        require(result['stdout'] == expected, 'nonpublic/unexpected output')
        return {'stdout': result['stdout'].decode('ascii'), 'stderr': ''}

    def close(self):
        for row in self.rows.values():
            for k in ('r','w'):
                if row[k] is not None:
                    os.close(row[k])
                    row[k] = None
        if self.parent is not None:
            os.close(self.parent)
            self.parent = None


def validate_manifest(m):
    from SbfFinite_validate import validate
    return validate({'schema':'SbfFinite-runtime-v1','runtime':m})

