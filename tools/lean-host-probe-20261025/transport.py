"""Disabled one-shot transport. Only unit tests may inject a mock Popen."""
import hashlib
import json
import os
import resource
import selectors
import stat
import subprocess
import sys
import time

ALLOCATED = True
ROOT = '/Users/dominic/ZK/.worktrees/cx-lean-host-probe/tools/lean-host-probe-20261025'
CAPTURE = '/private/tmp/lean-host-probe-20261025-capture-v1'
ARGV = ('/usr/bin/ssh', '-T', '-oBatchMode=yes', '-oConnectTimeout=10',
        '-oStrictHostKeyChecking=yes', '-oClearAllForwardings=yes', '-oForwardAgent=no',
        'dombarker@100.108.41.90', '/usr/bin/python3 -I -B -')
DISABLED_TAIL = "if __name__ == '__main__':\n    raise SystemExit('DISABLED: source-only payload; no host observations authorized')\n"
PAYLOAD_SHA = 'b99e3cb2a16858038ae462f28250dd72f539a09a6258d34d6213b6e4c3e796db'
FOOTER_SHA = '078eab79386ed58d91e6c2bdf01c3be261be9e4c277dd909deeca70e6c19ef41'
BODY_SHA = 'a0e950c2a8b418a43a110ecdeb9eb1c49e5b4cc45c6536f4f97b9530db734814'
CAP = 1024 * 1024


def pinned_read(name, digest):
    path = ROOT + '/' + name
    fds, edges = [], []
    try:
        fd = os.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_NONBLOCK)
        fds.append(fd)
        parts = path[1:].split('/')
        for i, part in enumerate(parts):
            before = os.stat(part, dir_fd=fd, follow_symlinks=False)
            directory = i < len(parts)-1
            if not (stat.S_ISDIR(before.st_mode) if directory else stat.S_ISREG(before.st_mode)):
                raise RuntimeError('source shape')
            flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
            if directory:
                flags |= os.O_DIRECTORY
            child = os.open(part, flags, dir_fd=fd)
            fds.append(child)
            edges.append((fd, part, child, before))
            fd = child
        s = os.fstat(fd)
        if s.st_uid != os.getuid() or s.st_nlink != 1 or s.st_size > CAP:
            raise RuntimeError('source owner/link/size')
        content = bytearray()
        while len(content) < s.st_size:
            b = os.read(fd, min(65536, s.st_size-len(content)))
            if not b:
                raise RuntimeError('short source')
            content.extend(b)
        def ident(x):
            return (x.st_dev, x.st_ino, x.st_mode, x.st_uid, x.st_gid,
                    x.st_nlink, x.st_size, x.st_mtime_ns, x.st_ctime_ns)
        for parent, name, child, before in edges:
            if ident(before) != ident(os.fstat(child)) or ident(before) != ident(os.stat(name, dir_fd=parent, follow_symlinks=False)):
                raise RuntimeError('source drift')
        if hashlib.sha256(content).hexdigest() != digest:
            raise RuntimeError('source hash')
        return bytes(content)
    finally:
        for fd in reversed(fds):
            os.close(fd)


def body():
    source = pinned_read('payload.py', PAYLOAD_SHA)
    footer = pinned_read('footer.py.txt', FOOTER_SHA)
    tail = DISABLED_TAIL.encode()
    if not source.endswith(tail):
        raise RuntimeError('disabled footer mismatch')
    b = source[:-len(tail)] + footer
    if hashlib.sha256(b).hexdigest() != BODY_SHA:
        raise RuntimeError('prospective body hash')
    return b


def exclusive(fd, name, data):
    f = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=fd)
    try:
        view = memoryview(data)
        while view:
            n = os.write(f, view)
            if n <= 0:
                raise RuntimeError('short receipt write')
            view = view[n:]
        os.fsync(f)
    finally:
        os.close(f)
    os.fsync(fd)


def collect(child, data, deadline):
    out, err = bytearray(), bytearray()
    with selectors.DefaultSelector() as sel:
        for stream, event, tag in ((child.stdin, selectors.EVENT_WRITE, 'in'),
                                   (child.stdout, selectors.EVENT_READ, 'out'),
                                   (child.stderr, selectors.EVENT_READ, 'err')):
            os.set_blocking(stream.fileno(), False)
            sel.register(stream, event, tag)
        offset = 0
        while sel.get_map():
            remaining = deadline-time.monotonic()
            if remaining <= 0:
                raise TimeoutError('local 20 second deadline')
            for key, _ in sel.select(min(remaining, 0.1)):
                if key.data == 'in':
                    try:
                        offset += os.write(key.fd, data[offset:offset+65536])
                    except BlockingIOError:
                        continue
                    if offset == len(data):
                        sel.unregister(key.fileobj)
                        key.fileobj.close()
                else:
                    b = os.read(key.fd, min(65536, CAP-len(out)-len(err)+1))
                    if not b:
                        sel.unregister(key.fileobj)
                        key.fileobj.close()
                    elif len(out)+len(err)+len(b) > CAP:
                        raise RuntimeError('combined output exceeds 1 MiB')
                    else:
                        (out if key.data == 'out' else err).extend(b)
        child.wait(timeout=max(0.001, deadline-time.monotonic()))
    return bytes(out), bytes(err)


def measurements(started):
    own = resource.getrusage(resource.RUSAGE_SELF)
    child = resource.getrusage(resource.RUSAGE_CHILDREN)
    scale = 1 if sys.platform == 'darwin' else 1024
    return {'wall_seconds': time.monotonic()-started,
            'self_peak_rss_bytes': own.ru_maxrss*scale,
            'child_peak_rss_bytes': child.ru_maxrss*scale,
            'self_swap_counter': own.ru_nswap, 'child_swap_counter': child.ru_nswap,
            'swap_bytes': 'unobserved', 'remote_rss_swap': 'unobserved',
            'axioms': 'N/A: metadata, no Lean invocation'}


def run_once(*, popen=subprocess.Popen, collector=collect):
    if not ALLOCATED:
        raise RuntimeError('DISABLED: lead allocation required')
    if os.path.abspath(__file__) != ROOT + '/transport.py':
        raise RuntimeError('reviewed source root mismatch')
    data = body()
    # A fixed fresh directory is mandatory. Existing paths are never adopted.
    os.mkdir(CAPTURE, 0o700)
    parent = os.open('/private/tmp', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(parent)
    finally:
        os.close(parent)
    fd = os.open(CAPTURE, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    child = None
    started = time.monotonic()
    try:
        s = os.fstat(fd)
        if s.st_uid != os.getuid() or stat.S_IMODE(s.st_mode) != 0o700:
            raise RuntimeError('capture owner/mode')
        exclusive(fd, 'charge.json', json.dumps({'attempt': 1, 'argv': ARGV,
                  'body_sha256': BODY_SHA, 'payload_sha256': PAYLOAD_SHA,
                  'footer_sha256': FOOTER_SHA,
                  'source_revision': 'b2c335bc89bb5dba0389d34b057bf22689ada592 plus reviewed source seals',
                  'status': 'charged_before_Popen_no_retry',
                  'axioms': 'N/A', 'proof_calls': 0}, sort_keys=True).encode()+b'\n')
        # This is the only Popen site; charge and directory entries are durable first.
        child = popen(ARGV, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                      stderr=subprocess.PIPE, shell=False, close_fds=True)
        out, err = collector(child, data, started + 20)
        exclusive(fd, 'stdout.json', out)
        exclusive(fd, 'stderr.txt', err)
        exclusive(fd, 'result.json', json.dumps({'exit': child.returncode,
                  **measurements(started), 'status': 'completed',
                  'scope': 'metadata_only_not_build_admission'}, sort_keys=True).encode()+b'\n')
    except BaseException as e:
        if child is not None and child.poll() is None:
            child.kill()
            child.wait(timeout=2)
        exclusive(fd, 'failure.json', json.dumps({'error_type': type(e).__name__,
                  **measurements(started), 'exit': None if child is None else child.returncode, 'retry': False}).encode()+b'\n')
        raise
    finally:
        if child is not None:
            for stream in (child.stdin, child.stdout, child.stderr):
                if stream is not None:
                    stream.close()
        os.close(fd)


if __name__ == '__main__':
    if not ALLOCATED:
        raise SystemExit('DISABLED: no SSH, host, compiler, version or help action authorized')
    run_once()
