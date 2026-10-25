if __name__ == '__main__':
    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')
"""Unexecuted Linux 6.8 x86_64 ABI. Import is pure; no CDLL at import.

Syscalls use individual complete typed signatures at
libc's syscall address, including the syscall-number long. No untyped pointer
arguments and no architecture fallback. ENOSYS/EINVAL/EPERM all fail closed.
"""
import ctypes as C
import platform
from SbfFiniteLinux_capture import Denied, require

I, U, L, Q, P, S = C.c_int, C.c_uint, C.c_long, C.c_uint64, C.c_void_p, C.c_char_p
EMPTY, RECURSIVE, CLOEXEC = 0x1000, 0x8000, 0x80000
RDONLY, NOSUID, NODEV, NOEXEC = 1, 2, 4, 8
PRIVATE = 1 << 18
NEWNS, NEWPID, NEWNET = 0x20000, 0x20000000, 0x40000000

class MountAttr(C.Structure):
    _fields_ = [(x, Q) for x in ('attr_set','attr_clr','propagation','userns_fd')]

class CapHeader(C.Structure):
    _fields_ = [('version', U), ('pid', I)]

class CapData(C.Structure):
    _fields_ = [('effective', U), ('permitted', U), ('inheritable', U)]

class Timestamp(C.Structure):
    _fields_ = [('sec', C.c_int64), ('nsec', U), ('reserved', I)]

class Statx(C.Structure):
    _fields_ = [('mask', U), ('blksize', U), ('attributes', Q),
        ('nlink', U), ('uid', U), ('gid', U), ('mode', C.c_uint16),
        ('spare0', C.c_uint16), ('ino', Q), ('size', Q), ('blocks', Q),
        ('attributes_mask', Q), ('atime', Timestamp), ('btime', Timestamp),
        ('ctime', Timestamp), ('mtime', Timestamp), ('rdev_major', U),
        ('rdev_minor', U), ('dev_major', U), ('dev_minor', U), ('mnt_id', Q),
        ('dio_mem_align', U), ('dio_offset_align', U), ('spare3', Q * 12)]

class Rlimit(C.Structure):
    _fields_ = [('cur', Q), ('max', Q)]

# syscall_64.tbl and include/linux/syscalls.h, pinned in reference manifest.
SPECS = {
 'unshare': (272, (C.c_ulong,)),
 'open_tree': (428, (I, S, U)),
 'move_mount': (429, (I, S, I, S, U)),
 'fsopen': (430, (S, U)),
 'fsconfig': (431, (I, U, S, P, I)),
 'fsmount': (432, (I, U, U)),
 'mount_setattr': (442, (I, S, U, C.POINTER(MountAttr), C.c_size_t)),
 'statx': (332, (I, S, U, U, C.POINTER(Statx))),
 'prctl': (157, (I, C.c_ulong, C.c_ulong, C.c_ulong, C.c_ulong)),
 'capget': (125, (C.POINTER(CapHeader), C.POINTER(CapData))),
 'capset': (126, (C.POINTER(CapHeader), C.POINTER(CapData))),
 'setgroups': (116, (I, C.POINTER(U))),
 'setresgid': (119, (U, U, U)), 'setresuid': (117, (U, U, U)),
 'close_range': (436, (U, U, U)),
 'pidfd_open': (434, (I, U)),
 'pidfd_send_signal': (424, (I, I, P, U)),
 'getrlimit': (97, (U, C.POINTER(Rlimit))),
 'setrlimit': (160, (U, C.POINTER(Rlimit))),
}


def layout_check():
    require(C.sizeof(P) == C.sizeof(L) == 8, 'LP64 required')
    for typ, size in ((MountAttr,32),(CapHeader,8),(CapData,12),
                      (Timestamp,16),(Statx,256),(Rlimit,16)):
        require(C.sizeof(typ) == size, 'ABI size '+typ.__name__)
    require(Statx.mnt_id.offset == 144 and Statx.atime.offset == 64 and
            MountAttr.propagation.offset == 16,
            'ABI offsets')


def supported(system=None, machine=None):
    require((system if system is not None else platform.system()) == 'Linux' and
            (machine if machine is not None else platform.machine()) == 'x86_64',
            'Linux x86_64 only; no C library loaded')
    layout_check()


class LinuxABI:
    """Internal source API, NOT an admission/authority interface.

    Constructing with real libc is prohibited by this job. Future reviewed root
    helper alone may construct this after fresh producer/scope/runtime gates.
    Tests supply a mock binder, never a C-library loader.
    """
    def __init__(self, binder=None, system=None, machine=None):
        supported(system, machine)  # before library/binder effects
        if binder is None:
            require(platform.release().split('.')[:2] == ['6','8'], 'unreviewed kernel release')
            libc = C.CDLL('libc.so.6', use_errno=True)
            address = C.cast(libc.syscall, P).value
            self._libc = libc
            binder = lambda name,types: C.CFUNCTYPE(L,L,*types,use_errno=True)(address)
        self.functions = {name: binder(name, types) for name, (_,types) in SPECS.items()}

    def call(self, name, *args):
        number, types = SPECS[name]
        require(len(args) == len(types), 'syscall arity')
        C.set_errno(0)
        result = self.functions[name](L(number), *args)
        if result == -1:
            error = C.get_errno()
            require(error > 0, 'missing syscall errno')
            raise OSError(error, name)
        require(type(result) is int and result >= 0, 'invalid syscall result')
        return result

    def zero(self, name, *args):
        require(self.call(name, *args) == 0, 'nonzero '+name)

    def attr(self, fd, bits=0, propagation=0, recursive=False):
        attr = MountAttr(bits, 0, propagation, 0)
        self.zero('mount_setattr', I(fd), b'', U(EMPTY | (RECURSIVE if recursive else 0)),
                  C.byref(attr), C.c_size_t(C.sizeof(attr)))

    def tree(self, fd):
        return self.call('open_tree', I(fd), b'', U(EMPTY | CLOEXEC | 1 | 0x100 | 0x800))

    def attach(self, mountfd, targetfd):
        self.zero('move_mount', I(mountfd), b'', I(targetfd), b'', U(0x44))

    def mount_id(self, fd):
        result = Statx()
        self.zero('statx', I(fd), b'', U(EMPTY | 0x100 | 0x800), U(0x1000), C.byref(result))
        require(result.mask & 0x1000 and result.mnt_id > 0, 'missing actual mount ID')
        return result.mnt_id

    def filesystem(self, kind, close):
        require(kind in ('tmpfs','proc'), 'fixed filesystems only')
        context = self.call('fsopen', kind.encode(), U(1))
        try:
            if kind == 'tmpfs':
                for key, value in ((b'size',b'1048576'),(b'nr_inodes',b'64'),
                                   (b'mode',b'1777'),(b'uid',b'0'),(b'gid',b'0')):
                    buf = C.create_string_buffer(value)
                    self.zero('fsconfig', I(context), U(1), key, C.cast(buf,P), I(0))
            self.zero('fsconfig', I(context), U(6), None, None, I(0))
            bits = NOSUID | NODEV | NOEXEC | (RDONLY if kind == 'proc' else 0)
            return self.call('fsmount', I(context), U(1), U(bits))
        finally:
            close(context)

    def prctl(self, option, arg=0, arg2=0):
        return self.call('prctl', I(option), C.c_ulong(arg),
                         C.c_ulong(arg2), C.c_ulong(0), C.c_ulong(0))

    def check_owned_signal(self, pidfd):
        self.zero('pidfd_send_signal', I(pidfd), I(0), None, U(0))

    def kill_owned(self, pidfd):
        self.zero('pidfd_send_signal', I(pidfd), I(9), None, U(0))

    def close_escape_fds(self):
        self.zero('close_range', U(3), U(0xffffffff), U(0))

    def guest_limits(self):
        # Only after close_range; no host limits, AS/DATA or limit increases.
        for resource, bound in ((7,256),(1,16384)):
            old = Rlimit()
            self.zero('getrlimit', U(resource), C.byref(old))
            require(old.cur >= bound and old.max >= bound, 'guest limit would increase')
            limit = Rlimit(bound,bound)
            self.zero('setrlimit', U(resource), C.byref(limit))

    def drop(self, last_cap):
        require(last_cap == 40, 'kernel capability ABI differs from pinned 6.8')
        self.zero('setgroups', I(0), None)
        require(self.prctl(47,4) == 0, 'ambient clear')
        for cap in range(last_cap+1):
            require(self.prctl(24,cap) == 0, 'bounding drop')
        self.zero('setresgid', U(1000), U(1000), U(1000))
        self.zero('setresuid', U(1000), U(1000), U(1000))
        header, data = CapHeader(0x20080522,0), (CapData*2)()
        self.zero('capset', C.byref(header), data)
        require(self.prctl(38,1) == 0 and self.prctl(39) == 1, 'NNP')
        self.zero('capget', C.byref(header), data)
        require(header.version == 0x20080522 and
                all(d.effective == d.permitted == d.inheritable == 0 for d in data),
                'capget residual')
        for cap in range(last_cap+1):
            require(self.prctl(23,cap) == self.prctl(47,1,cap) == 0,
                    'bounding/ambient residual')
