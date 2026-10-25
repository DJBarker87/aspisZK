"""Pure-testable finite metadata operations. No traversal of unlisted files.

New implementation, not a byte-identical claim about the old walker. All
filesystem operations are injectable; tests supply an entirely synthetic FS.
"""
import os
import stat
import hashlib

PUBLIC = ('/usr/bin', '/usr/lib', '/usr/local/lib')
PREFIX = ('/lib', '/lib64', '/usr/lib64')
SSL = ('/usr/lib/ssl/openssl.cnf', '/etc/ssl/openssl.cnf')
CONFIG = ('/etc/ld.so.cache', '/etc/ld.so.preload', '/etc/localtime') + SSL
DIR = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
FILE = os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK


def under(path, roots):
    return any(path == r or path.startswith(r + '/') for r in roots)


def lexical(path):
    if not isinstance(path, str) or not path.startswith('/') or len(path) >= 4096 or not path.isascii():
        raise ValueError('path syntax')
    if any(p in ('', '.', '..', 'site-packages', 'dist-packages') or p.startswith('.') or
           any(ord(c) < 33 or ord(c) > 126 for c in p) for p in path.split('/')[1:]):
        raise ValueError('path components')
    return path


def permitted(original, endpoint, final=False):
    # SSL is an exact two-endpoint grammar, not an /etc/ssl subtree grant.
    if original in SSL:
        return endpoint in SSL
    if original == '/etc/localtime':
        return endpoint == original or under(endpoint, ('/usr/share/zoneinfo',))
    if original in ('/etc/ld.so.cache', '/etc/ld.so.preload'):
        return endpoint == original  # no config redirect into arbitrary public data
    return under(endpoint, PUBLIC if final else PUBLIC + PREFIX)


def identity(s):
    return [getattr(s, k) for k in ('st_dev', 'st_ino', 'st_mode', 'st_uid', 'st_gid',
            'st_nlink', 'st_size', 'st_mtime_ns', 'st_ctime_ns')]


def owned(s, symlink=False):
    if s.st_uid != 0 or s.st_gid != 0 or (not symlink and s.st_mode & 0o022):
        raise ValueError('ownership/mode')
    if symlink and s.st_nlink != 1:
        raise ValueError('symlink link count')


def acquire(path, attempts, fs, limit=16*2**20, check=lambda: None, admit=lambda physical, s: None):
    """Return bytes/metadata after checking every held FD and named entry.

    Directories stay open across link restarts and through the final read.
    Rechecks detect observed races; root/kernel adversaries remain outside the
    inherited boundary. This does not prove historical open-to-inode identity.
    """
    row = dict(path=path, status='ATTEMPT', chain=[], symlinks=[])
    attempts.append(row)
    fds, entries, descriptors = [], [], []
    try:
        lexical(path)
        if not (under(path, PUBLIC + PREFIX) or path in CONFIG):
            raise ValueError('outside explicit paths')
        todo, done, seen = path.split('/')[1:], [], set()
        def root():
            fd = fs.open('/', DIR)
            fds.append(fd)
            s = fs.fstat(fd)
            owned(s)
            if not stat.S_ISDIR(s.st_mode):
                raise ValueError('root type')
            descriptors.append((fd, identity(s)))
            row['chain'].append(dict(path='/', identity=identity(s)))
            return fd
        parent = root()
        while todo:
            check()
            name = todo.pop(0)
            current = '/' + '/'.join(done + [name])
            row['failed_component'] = current
            s = fs.stat(name, dir_fd=parent, follow_symlinks=False)
            link = stat.S_ISLNK(s.st_mode)
            owned(s, link)
            entries.append((parent, name, identity(s)))
            item = dict(path=current, identity=identity(s))
            row['chain'].append(item)
            if link:
                target = fs.readlink(name, dir_fd=parent)
                item['target'] = target
                row['symlinks'].append(item.copy())
                if identity(s) != identity(fs.stat(name, dir_fd=parent, follow_symlinks=False)):
                    raise ValueError('symlink drift')
                state = (current, tuple(todo))
                if state in seen or len(row['symlinks']) > 16:
                    raise ValueError('symlink loop/depth')
                seen.add(state)
                combined = target if target.startswith('/') else '/' + '/'.join(done + [target])
                resolved = os.path.normpath(combined + ('/' + '/'.join(todo) if todo else ''))
                lexical(resolved)
                if not permitted(path, resolved):
                    raise ValueError('symlink endpoint outside exact grammar: ' + resolved)
                todo, done, parent = resolved.split('/')[1:], [], root()
                continue
            if todo and not stat.S_ISDIR(s.st_mode):
                raise ValueError('non-directory ancestor')
            if not todo and not permitted(path, current, final=True):
                raise ValueError('final endpoint outside exact grammar')
            if not todo and not (stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode)):
                raise ValueError('unsupported endpoint')
            fd = fs.open(name, DIR if stat.S_ISDIR(s.st_mode) else FILE, dir_fd=parent)
            fds.append(fd)
            if identity(s) != identity(fs.fstat(fd)):
                raise ValueError('entry/FD drift')
            descriptors.append((fd, identity(s)))
            if todo:
                done.append(name)
                parent = fd
                continue
            raw = None
            if stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1 or s.st_size < 0 or s.st_size > limit:
                    raise ValueError('regular link/size bound')
                admit(current, s)  # bound unique files/bytes BEFORE reading/hashing
                chunks, count = [], 0
                while True:
                    check()
                    part = fs.read(fd, min(65536, s.st_size + 1 - count))
                    if not part:
                        break
                    count += len(part)
                    if count > s.st_size:
                        raise ValueError('file grew')
                    chunks.append(part)
                if count != s.st_size:
                    raise ValueError('file shrank')
                raw = b''.join(chunks)
            for d, before in descriptors:
                if before != identity(fs.fstat(d)):
                    raise ValueError('descriptor drift after read')
            for d, n, before in entries:
                if before != identity(fs.stat(n, dir_fd=d, follow_symlinks=False)):
                    raise ValueError('chain entry drift after read')
            row.update(status='DIRECTORY' if raw is None else 'PINNED', physical=current,
                       identity=identity(s), stable_fd=True, failed_component=None)
            if raw is not None:
                row.update(size=len(raw), sha256=hashlib.sha256(raw).hexdigest())
            return raw, row
        raise ValueError('empty endpoint')
    except (OSError, ValueError) as exc:
        row.update(status='ABSENT' if isinstance(exc, FileNotFoundError) else 'ERROR',
                   error_type=type(exc).__name__, error=str(exc), errno=getattr(exc, 'errno', None))
        return None, row
    finally:
        for fd in reversed(fds):
            fs.close(fd)


def pyc_header(raw):
    if len(raw) < 16:
        return dict(classification='REJECTED_SHORT_HEADER', header_hex=raw.hex())
    flags = int.from_bytes(raw[4:8], 'little')
    row = dict(header_hex=raw[:16].hex(), magic_hex=raw[:4].hex(), flags=flags,
               executed_bytecode_equality='OPEN; no marshal/body evaluation')
    if flags not in (0, 1, 3):
        row['classification'] = 'REJECTED_FLAGS'
    elif flags == 0:
        row.update(classification='TIMESTAMP', timestamp=int.from_bytes(raw[8:12], 'little'),
                   source_size=int.from_bytes(raw[12:16], 'little'))
    else:
        row.update(classification='CHECKED_HASH' if flags == 3 else 'UNCHECKED_HASH',
                   source_hash_hex=raw[8:16].hex(), source_hash_binding='UNVERIFIED')
    return row


def association(plan, outcomes):
    stale, incomplete = [], []
    for item in plan['paths']:
        path = item['path']
        if item['classification'] == 'OWN_PROC_METADATA_NOT_REACQUIRED':
            continue
        result = outcomes[path]
        old = item.get('old_pin')
        expected_status = 'DIRECTORY' if item['classification'] == 'DIRECTORY_METADATA' else 'PINNED'
        if result['status'] != expected_status:
            incomplete.append(path)
        known_chain = item.get('old_chain', [])
        fresh = {r['path']:r['identity'] for r in result.get('chain', [])}
        chain_drift = any(fresh.get(r['path']) != r['identity'] for r in known_chain)
        if chain_drift:
            stale.append(path)
        if old and (result['status'] != 'PINNED' or
                    any(result.get(k) != old[k] for k in ('sha256', 'size', 'identity')) or
                    result.get('physical') != old['physical']):
            stale.append(path)
    return dict(oldtrace_association='STALE' if stale else 'REUSED_MATCHING_AVAILABLE_PINS_ONLY',
                drift_paths=sorted(set(stale)), incomplete_paths=incomplete,
                eligible_candidate=not stale and not incomplete,
                open_fd_to_later_inode='OPEN even when all later hashes/identities match',
                automatic_retrace=False)


def correspondence(modules, outcomes):
    rows = []
    for name, module in sorted(modules.items()):
        row = dict(module=name, source=module.get('file'), cache=module.get('cached'),
                   executed_bytecode_equality='OPEN')
        source, cache = (outcomes.get(module.get(k), {}) for k in ('file', 'cached'))
        row.update(source_status=source.get('status', 'NO_PATH'), cache_status=cache.get('status', 'NO_PATH'))
        header = cache.get('pyc')
        if header:
            row['header'] = header
            if header['classification'] == 'TIMESTAMP' and source.get('status') == 'PINNED':
                row['timestamp_size_match'] = (header['timestamp'] == (source['identity'][7] // 10**9) & 0xffffffff
                                               and header['source_size'] == source['size'] & 0xffffffff)
        rows.append(row)
    return rows


def candidate(plan, outcomes, state):
    # Logical aliases are literal plan paths with complete fresh chains. Every
    # byte clone counts independently. No basename/SONAME inference.
    files, logicals, total = [], set(), 0
    for item in plan['paths']:
        if item['classification'] != 'FILE_CANDIDATE':
            continue
        row = outcomes[item['path']]
        if row['status'] != 'PINNED':
            continue
        for logical in (item['path'], row['physical']):
            if logical in logicals:
                continue
            logicals.add(logical)
            total += row['size']
            files.append(dict(logical=logical, physical=row['physical'], size=row['size'],
                              sha256=row['sha256'], mode=0o555 if row['identity'][2] & 0o111 else 0o444))
    return dict(manifest=dict(plan['candidate_template'], files=files), status='PROSPECTIVE_INPUT_DATA_ONLY',
                copied_bytes=total, eligible_candidate=state['eligible_candidate'] and total <= 64*2**20 and 0 < len(files) <= 256,
                guest_copy_cap=64*2**20, runtime_approval=None, security_approval=None,
                tool_dependencies=plan['tool_dependencies'])
