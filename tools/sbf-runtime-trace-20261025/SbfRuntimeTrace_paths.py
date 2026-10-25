"""Finite root-owned walk. Attempts, including failures, are durable data.

No permission follows from a trace pathname. Symlinks use ordinary 0777 link
mode; non-writability applies to every containing directory and regular file.
"""
import os
import stat

PUBLIC = ('/usr/bin', '/usr/lib', '/usr/local/lib')
ALIASES = ('/lib', '/lib64', '/usr/lib64')
CONFIG = ('/etc/ld.so.cache', '/etc/ld.so.preload', '/etc/localtime', '/etc/ssl/openssl.cnf')
CONFIG_TARGETS = ('/usr/share/zoneinfo', '/usr/lib/ssl', '/etc/ssl')

def under(path, roots):
    return any(path == p or path.startswith(p + '/') for p in roots)

def lexical(path):
    if not isinstance(path, str) or not path.startswith('/') or len(path) >= 4096 or not path.isascii():
        raise ValueError('path syntax')
    if any(p in ('', '.', '..') or p.startswith('.') or p in ('site-packages', 'dist-packages') or
           any(ord(c) < 33 or ord(c) > 126 for c in p) for p in path.split('/')[1:]):
        raise ValueError('path components')
    return path

def identity(s):
    return tuple(getattr(s, k) for k in ('st_dev', 'st_ino', 'st_mode', 'st_uid', 'st_gid',
                  'st_nlink', 'st_size', 'st_mtime_ns', 'st_ctime_ns'))

def walk(path, attempts, fs=os):
    row = dict(path=path, status='ATTEMPT', components=[], symlinks=[], failed_component=None)
    attempts.append(row)  # BEFORE syntax, stat, or ownership operations
    fd = None
    try:
        lexical(path)
        config = path in CONFIG
        if not (under(path, PUBLIC + ALIASES) or config):
            raise ValueError('outside explicit observation paths')
        todo = path.split('/')[1:]
        done = []
        seen = set()
        fd = fs.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC)
        root = fs.fstat(fd)
        if root.st_uid != 0 or root.st_mode & 0o022:
            raise ValueError('root ownership/mode')
        while todo:
            name = todo.pop(0)
            current = '/' + '/'.join(done + [name])
            row['failed_component'] = current
            s = fs.stat(name, dir_fd=fd, follow_symlinks=False)
            item = dict(path=current, identity=list(identity(s)))
            row['components'].append(item)
            if s.st_uid != 0:
                raise ValueError('non-root component: ' + current)
            if stat.S_ISLNK(s.st_mode):
                target = fs.readlink(name, dir_fd=fd)
                item['target'] = target
                row['symlinks'].append(item.copy())
                if identity(s) != identity(fs.stat(name, dir_fd=fd, follow_symlinks=False)):
                    raise ValueError('symlink drift')
                state = (current, tuple(todo))
                if state in seen or len(row['symlinks']) > 16:
                    raise ValueError('symlink loop/depth')
                seen.add(state)
                combined = target if target.startswith('/') else '/' + '/'.join(done + [target])
                normalized = os.path.normpath(combined)
                lexical(normalized)
                allowed_config = (path == '/etc/localtime' and under(normalized, ('/usr/share/zoneinfo',)) or
                                  path == '/etc/ssl/openssl.cnf' and under(normalized, ('/usr/lib/ssl','/etc/ssl')))
                if not (under(normalized, PUBLIC + ALIASES) or config and allowed_config):
                    raise ValueError('symlink outside explicit paths: ' + normalized)
                todo = normalized.split('/')[1:] + todo
                done = []
                fs.close(fd)
                fd = None
                fd = fs.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC)
                root = fs.fstat(fd)
                if root.st_uid != 0 or root.st_mode & 0o022:
                    raise ValueError('root drift')
                continue
            if s.st_mode & 0o022:
                raise ValueError('writable component: ' + current)
            if todo:
                if not stat.S_ISDIR(s.st_mode):
                    raise ValueError('non-directory ancestry')
                child = fs.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=fd)
                if identity(s) != identity(fs.fstat(child)):
                    fs.close(child)
                    raise ValueError('directory drift')
                fs.close(fd)
                fd = child
                done.append(name)
            else:
                allowed_config = (current == path or
                                  path == '/etc/localtime' and under(current, ('/usr/share/zoneinfo',)) or
                                  path == '/etc/ssl/openssl.cnf' and under(current, ('/usr/lib/ssl','/etc/ssl')))
                if not (under(current, PUBLIC) or config and allowed_config):
                    raise ValueError('final endpoint outside original roots')
                if not (stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode)):
                    raise ValueError('unsupported file type')
                row.update(status='OBSERVED', physical=current, failed_component=None)
                return current, s, row
        raise ValueError('empty endpoint')
    except BaseException as exc:
        row.update(status='FAILED', error_type=type(exc).__name__, errno=getattr(exc, 'errno', None),
                   error=str(exc))
        raise
    finally:
        if fd is not None:
            fs.close(fd)
