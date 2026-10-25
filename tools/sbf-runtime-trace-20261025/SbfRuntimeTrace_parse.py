"""Conservative single-tracee parser; unknown state denies completeness.

Every raw line survives in events, including unpaired split records. This is
metadata interpretation, never an open-to-inode identity proof.
"""
import ast
import os
import re

def split_args(text):
    out, start, stack, quoted, escaped = [], 0, [], False, False
    for i, c in enumerate(text):
        if quoted:
            if escaped: escaped = False
            elif c == '\\': escaped = True
            elif c == '"': quoted = False
        elif c == '"': quoted = True
        elif c in '([{': stack.append(c)
        elif c in ')]}':
            if not stack or '([{'.index(stack.pop()) != ')]}'.index(c): raise ValueError('argument brackets')
        elif c == ',' and not stack:
            out.append(text[start:i].strip()); start = i + 1
    if quoted or stack: raise ValueError('incomplete arguments')
    return out + [text[start:].strip()]

def string(value):
    if not re.fullmatch(r'"(?:[^"\\]|\\.)*"', value): raise ValueError('nonliteral/truncated path')
    result = ast.literal_eval(value)
    if not isinstance(result, str) or '\x00' in result: raise ValueError('invalid path')
    return result

def fdnum(value):
    m = re.fullmatch(r'(-?\d+)(?:<([^\n]*)>)?', value)
    if not m: raise ValueError('FD syntax: ' + value)
    return int(m[1]), m[2]

def parse(raw, expected_pid=None):
    result = dict(complete=False, events=[], errors=[], opens=[], negatives=[], mapped=[],
                  positive_paths=[], identity_association='OPEN; pathname/FD labels are not inode pins')
    states, pending, pids, execs = {}, {}, set(), 0
    def path_at(value, dirfd, fds):
        p = string(value)
        if p.startswith('/'): return p
        if dirfd == 'AT_FDCWD': raise ValueError('relative path with unknown cwd')
        n, label = fdnum(dirfd)
        base = fds.get(n)
        if not base or not base.startswith('/'): raise ValueError('unknown dirfd')
        if label is not None and label != base: raise ValueError('dirfd annotation mismatch')
        return os.path.normpath(base + '/' + p)
    for index, line in enumerate(raw.splitlines()):
        event = dict(index=index, raw=line)
        result['events'].append(event)
        try:
            m = re.fullmatch(r'(\d+)\s+(\d+\.\d+)\s+(.*)', line)
            if not m: raise ValueError('missing PID/timestamp')
            pid, stamp, body = int(m[1]), m[2], m[3]
            pids.add(pid); event.update(pid=pid, timestamp=stamp)
            if expected_pid is not None and pid != expected_pid: raise ValueError('unauthorized process/thread')
            if len(pids) != 1: raise ValueError('multiple tracee identities')
            fds = states.setdefault(pid, {0:'STDIN', 1:'STDOUT', 2:'STDERR'})
            if body.endswith('<unfinished ...>'):
                if pid in pending: raise ValueError('duplicate unfinished')
                pending[pid] = (body[:-len('<unfinished ...>')], index)
                event['unfinished'] = True
                continue
            if body.startswith('<... '):
                r = re.fullmatch(r'<\.\.\. (\w+) resumed>(.*)', body)
                if not r or pid not in pending: raise ValueError('unmatched resumed')
                first, earlier = pending.pop(pid)
                if not first.startswith(r[1] + '('): raise ValueError('resumed syscall mismatch')
                event['resumes'] = earlier
                body = first + r[2]
            if re.fullmatch(r'\+\+\+ exited with \d+ \+\+\+', body):
                event['exit'] = body
                continue
            if body.startswith('--- '): raise ValueError('signal record requires review')
            call = re.fullmatch(r'(\w+)\((.*)\)\s+=\s+(.*)', body)
            if not call: raise ValueError('unknown record')
            name, text, ret = call.groups()
            args = split_args(text)
            event.update(syscall=name, args=args, result=ret)
            failed = ret.startswith('-1 ')
            paths = []
            if name in ('openat', 'openat2', 'newfstatat', 'faccessat', 'faccessat2', 'readlinkat', 'statx'):
                if len(args) < 2: raise ValueError('short dirfd syscall')
                if args[1] == '""' and name in ('newfstatat', 'statx') and 'AT_EMPTY_PATH' in text:
                    n, label = fdnum(args[0])
                    if n not in fds: raise ValueError('empty path unknown FD')
                    event['fd_path'] = fds[n]
                else: paths = [path_at(args[1], args[0], fds)]
            elif name in ('open', 'access', 'stat', 'lstat', 'readlink', 'execve'):
                paths = [path_at(args[0], 'AT_FDCWD', fds)]
            elif name in ('close', 'dup', 'dup2', 'dup3', 'fcntl', 'mmap', 'munmap', 'exit_group', 'exit'):
                pass
            elif name in ('clone', 'clone3', 'fork', 'vfork', 'execveat'):
                raise ValueError('unauthorized process/shared-files/exec transition')
            else: raise ValueError('unsupported syscall/state: ' + name)
            event['paths'] = paths
            if failed:
                errno = ret.split()[1]
                result['negatives'].append(dict(index=index, syscall=name, paths=paths, errno=errno))
                continue
            result['positive_paths'].extend(dict(index=index, syscall=name, path=p) for p in paths)
            if name == 'execve':
                execs += 1
                if execs != 1 or paths != ['/usr/bin/python3']: raise ValueError('unexpected exec target/count')
                # At first exec only inherited standard streams are authorized.
                if set(fds) != {0,1,2}: raise ValueError('unknown exec descriptor state')
            elif name in ('open', 'openat', 'openat2'):
                if any(flag in text for flag in ('O_WRONLY','O_RDWR','O_CREAT','O_TRUNC','O_APPEND')):
                    raise ValueError('unexpected write open')
                n, label = fdnum(ret)
                if n in fds: raise ValueError('open reused live descriptor')
                if label is not None and label != paths[0]:
                    event['physical_label_unproved'] = label
                fds[n] = paths[0]
                result['opens'].append(dict(index=index, pid=pid, fd=n, path=paths[0], fd_label=label,
                                            inode_association='OPEN'))
            elif name == 'close':
                n, label = fdnum(args[0])
                if n not in fds: raise ValueError('close unknown descriptor')
                event['fd_path'] = fds.pop(n)
            elif name in ('dup','dup2','dup3','fcntl'):
                n, label = fdnum(args[0])
                if n not in fds: raise ValueError('descriptor operation unknown source')
                if name == 'fcntl' and args[1] not in ('F_DUPFD','F_DUPFD_CLOEXEC'):
                    if args[1] not in ('F_GETFD','F_GETFL','F_SETFD'): raise ValueError('unknown fcntl effect')
                else:
                    dest, label2 = fdnum(ret)
                    if name in ('dup','fcntl') and dest in fds: raise ValueError('duplicate to live descriptor')
                    fds[dest] = fds[n]
                    event['fd_path'] = fds[n]
            elif name == 'mmap':
                if len(args) != 6: raise ValueError('mmap shape')
                n, label = fdnum(args[4])
                if n != -1:
                    if n not in fds: raise ValueError('mmap unknown descriptor')
                    result['mapped'].append(dict(index=index, path=fds[n], fd=n, label=label))
        except Exception as exc:
            event['error'] = str(exc)
            result['errors'].append(dict(index=index, error=str(exc)))
    for pid, (_, index) in pending.items():
        result['errors'].append(dict(index=index, error='unpaired unfinished', pid=pid))
    if execs != 1: result['errors'].append(dict(error='missing unique initial exec'))
    if not result['events'] or not any('exit' in e for e in result['events']):
        result['errors'].append(dict(error='missing complete exit record'))
    result.update(complete=not result['errors'], pids=sorted(pids), exec_count=execs,
                  opened_unmapped=sorted({o['path'] for o in result['opens']} - {m['path'] for m in result['mapped']}))
    return result
