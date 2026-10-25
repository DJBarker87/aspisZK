"""Fixed source package and journals. No install operation or runtime approval."""
import hashlib
import json
import os
import stat
from SbfProducerLinux_capture import (Denied, require, open_safe_ancestry,
    FILE_FLAGS, check_entry, identity)

PACKAGE = '/opt/aspis/SbfProducer-20261025-v1'
ROOT_JOURNAL = '/var/lib/SbfProducer-20261025-v1/journal-root'
USER_JOURNAL = '/home/dombarker/SbfProducer-20261025-v1-journal'
UNIT = 'SbfProducer-20261025-tiny-v1'
ENV = dict(PATH='/usr/bin', LC_ALL='C', HOME='/probe', TMPDIR='/tmp')
LAUNCHER = '/usr/local/libexec/SbfProducer-20261025-tiny-root'
SUDO = ('/usr/bin/sudo', '-n', '--', LAUNCHER)
SCOPE = ('/usr/bin/systemd-run', '--user', '--scope', '--unit='+UNIT,
         '-p', 'MemoryHigh=3G', '-p', 'MemoryMax=4G',
         '-p', 'MemorySwapMax=0', '-p', 'TasksMax=64',
         '/usr/bin/env', '-i', 'HOME=/probe', 'LC_ALL=C', 'PATH=/usr/bin',
         'TMPDIR=/tmp', '/usr/bin/python3', '-I', '-S', '-B',
         PACKAGE+'/SbfProducer_user_entry.py')


def digest(raw):
    return dict(sha256=hashlib.sha256(raw).hexdigest(), size=len(raw))


def pinned_file(path, pin, mode, api=os, ancestry=open_safe_ancestry):
    """Root-owned nofollow ancestry, regular single-link exact modes and bytes.

    Proc exe magic links are intentionally handled elsewhere, never here.
    A root adversary is outside this boundary, as in the reviewed backend.
    """
    directory, name = path.rsplit('/', 1)
    parent = ancestry(directory)
    fd = None
    try:
        fd = api.open(name, FILE_FLAGS, dir_fd=parent)
        before = api.fstat(fd)
        require(stat.S_ISREG(before.st_mode) and before.st_uid == 0 and
                before.st_gid == 0 and before.st_nlink == 1 and
                stat.S_IMODE(before.st_mode) == mode, 'package type/owner/mode/link')
        require(before.st_size == pin['size'] <= 64*2**20, 'package size')
        check_entry(parent, name, fd) if api is os else api.check_entry(parent, name, fd)
        pieces, total = [], 0
        while True:
            raw = api.read(fd, min(65536, pin['size']+1-total))
            if not raw:
                break
            pieces.append(raw)
            total += len(raw)
            require(total <= pin['size'], 'package grew')
        raw = b''.join(pieces)
        require(identity(before) == identity(api.fstat(fd)) and digest(raw) == pin,
                'package changed/digest')
        return raw
    finally:
        if fd is not None:
            api.close(fd)
        api.close(parent)


def no_duplicates(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, 'duplicate key')
        out[key] = value
    return out


def approval():
    from SbfProducer_pins import RUNTIME_PIN
    require(type(RUNTIME_PIN) is dict and set(RUNTIME_PIN) == {'sha256','size'},
            'published reviewed runtime closure unavailable')
    raw = pinned_file(PACKAGE+'/SbfProducer_runtime.json', RUNTIME_PIN, 0o444)
    value = json.loads(raw, object_pairs_hook=no_duplicates,
                       parse_constant=lambda _: require(False, 'nonfinite JSON'))
    require(set(value) == {'schema','runtime','host','roles','scope_path','limits','env'},
            'finite approval fields')
    require(value['schema'] == 'SbfProducer-runtime-v1' and value['env'] == ENV,
            'approval version/environment')
    require(value['scope_path'].endswith('/'+UNIT+'.scope'), 'approved scope path')
    return value


def verify_package():
    from SbfProducer_pins import FILES
    require(FILES and all('/' not in name and name.startswith('SbfProducer')
                         for name in FILES), 'fixed package file set')
    return {name:digest(pinned_file(PACKAGE+'/'+name, row['pin'], row['mode']))
            for name, row in sorted(FILES.items())}


def journal(name, value):
    """Exclusive full raw JSON retention, no public export of arbitrary content.

    Both fixed journal directories are prerequisites, not created by this API.
    Root never reads the user journal or accepts it as authority.
    """
    require(name in {'inside-scope-ordered.json','inside-scope-report.json',
                    'inside-scope-metrics.json','root-before.json','root-after.json',
                    'user-before.json','user-after.json','user-guard.json',
                    'root-result.json','failure.json'}, 'fixed journal name')
    root = os.geteuid() == 0
    if root:
        parent = open_safe_ancestry(ROOT_JOURNAL)
    else:
        parent = os.open(USER_JOURNAL, os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC)
        s = os.fstat(parent)
        if s.st_uid != os.getuid() or stat.S_IMODE(s.st_mode) != 0o700:
            os.close(parent)
            raise Denied('user journal owner/mode')
    fd = None
    try:
        fd = os.open(name, os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC, 0o600, dir_fd=parent)
        encoder = json.JSONEncoder(sort_keys=True)
        size = 0
        for chunk in encoder.iterencode(value):
            raw = chunk.encode()
            size += len(raw)
            require(size <= 128*2**20, 'raw journal bound')
            while raw:
                written = os.write(fd, raw)
                require(written > 0, 'journal short write')
                raw = raw[written:]
        os.fsync(fd)
    finally:
        if fd is not None:
            os.close(fd)
        os.close(parent)
