"""Reused immutable synthetic kernel constructors; no historical test suite."""
import contextlib
import os
from pathlib import Path
import subprocess
from types import SimpleNamespace
from unittest.mock import patch
import ResourceStableGO_adapter as a
from ResourceStableGO_sources import functions,load_bundle
fixtures=functions(load_bundle()['fixtures']['source'],['node','fixture','scope'],dict(c=a.c,G=a.c.GIB))
def fixture(ancestor=False):
    s, _ = fixtures['scope'](3 * a.c.GIB, 4 * a.c.GIB, ancestor)
    pid = os.getpid()
    row = s['rows'][-1]
    old = row['path']
    new = str(Path(old).with_name(a.UNIT + '.scope'))
    row.update(path=new, domain=new, procs=[pid], threads=[pid], identities=[dict(tid=pid, tgid=pid, starttime=123)])
    s['self_observation'].update(pid=pid, path=new, unified_path=new[len('/sys/fs/cgroup'):])
    return s

def virtual(s):
    """Exact synthetic kernel interfaces, not a supplied live identity."""
    files = {}
    directories = {}
    files['/proc/meminfo'] = ''.join((f'{k}: {v // 1024} kB\n' for k, v in s['meminfo'].items()))
    for row in s['rows']:
        p = row['path']
        directories[p] = [c['path'] for c in s['rows'] if c['parent'] == p]
        vals = {'cgroup.subtree_control': ' '.join((x for x, flag in [('memory', row['subtree_memory']), ('pids', row['subtree_pids'])] if flag)), 'cgroup.controllers': ' '.join(row['controllers']), 'cgroup.threads': ' '.join(map(str, row['threads'])), 'cgroup.procs': ' '.join(map(str, row['procs']))}
        if not row['root']:
            vals.update({'cgroup.type': row['type'], 'cgroup.events': f'populated {int(row['populated'])}\nfrozen 0'})
        if row['pids_enabled']:
            vals.update({'pids.max': row['tasks_max'], 'pids.current': row['pids_current']})
        if row['enabled']:
            for field, name in [('current', 'memory.current'), ('cap', 'memory.max'), ('high', 'memory.high'), ('swap_max', 'memory.swap.max'), ('swap_current', 'memory.swap.current')]:
                vals[name] = 'max' if row[field] is None else row[field]
            vals['memory.stat'] = ''.join((f'{k} {v}\n' for k, v in row['stat'].items()))
        for name, val in vals.items():
            files[p + '/' + name] = str(val).rstrip('\n') + '\n'
        for i in row['identities']:
            prefix = '/proc/' + str(i['tid'])
            pid = i['tid']
            files[prefix + '/stat'] = f'{pid} (ResourceStableGO synthetic) ' + ' '.join(['S'] + ['0'] * 18 + [str(i['starttime'])]) + '\n'
            files[prefix + '/status'] = f'Pid: {pid}\nTgid: {i['tgid']}\n'
            files[prefix + '/cgroup'] = '0::' + p[len('/sys/fs/cgroup'):] + '\n'
    own = s['self_observation']['pid']
    for name in ('stat', 'status', 'cgroup'):
        files['/proc/self/' + name] = files[f'/proc/{own}/' + name]

    def read(path, *args, **kwargs):
        path = str(path)
        if path not in files:
            raise FileNotFoundError(2, 'synthetic absent', path)
        value = files[path]
        if isinstance(value, Exception):
            raise value
        return value

    @contextlib.contextmanager
    def scandir(path):
        yield [SimpleNamespace(path=x, name=Path(x).name, is_dir=lambda **kw: True) for x in directories[str(path)]]

    def run(argv, *args, **kwargs):
        if argv == a.COMMANDS[0]:
            output = f'PID PPID RSS COMMAND CGROUP\n{own} 1 100 python {s['self_observation']['unified_path']}\n'
        elif argv == a.COMMANDS[1]:
            output = 'example.service loaded active running example\n'
        elif argv == a.COMMANDS[2]:
            output = ''
        else:
            raise AssertionError(('unexpected command', argv))
        return subprocess.CompletedProcess(argv, 0, output, '')
    return (files, read, scandir, run)

@contextlib.contextmanager
def kernel(s):
    files, read, scandir, run = virtual(s)
    with patch.object(Path, 'read_text', read), patch.object(os, 'scandir', scandir), patch.object(subprocess, 'run', run):
        yield files
