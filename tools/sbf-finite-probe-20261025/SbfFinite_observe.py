if __name__ == '__main__':
    raise SystemExit('SbfFinite SOURCE ONLY: disabled before imports')
"""Concrete reviewed operational functions; never called in this job.

Function text is identical to the renamed RssGOv3 host. Only the surrounding
bindings differ: exact new unit, root-owned raw journal and no old main/marker.
"""
import contextlib
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import struct
import subprocess
import sys
import sysconfig
import time
import SbfFiniteRss_adapter as adapter
from SbfFinite_package import journal as save
ACTIVE_GUARD = None
EXPECTED = dict(high=768*2**20, cap=2**30, swap_max=0, tasks_max=64)
adapter.UNIT = 'SbfFinite-20261025-tiny-v1'
def digest(raw):
    return dict(sha256=hashlib.sha256(raw).hexdigest(), size=len(raw))
def filepin(path):
    return digest(Path(path).read_bytes())


def runtime_pins():
    # Exact finite host-role paths published in separate operational data.
    # No broad filesystem discovery, dlopen, ldd, version/help probe or host shell.
    from SbfFinite_package import approval, pinned_file
    role = 'helper' if os.geteuid() == 0 else 'collector'
    expected = approval()['host'][role]
    if type(expected) is not dict or set(expected) != {'files'}:
        raise ValueError('finite host file catalog required')
    for p,item in sorted(expected['files'].items()):
        pinned_file(p,item['pin'],item['mode'])
    return expected

def collect(phase):
    """Record every ordered filesystem/command input without changing API logic."""
    api=adapter.__dict__
    events=[]
    read=Path.read_text
    execute=subprocess.run
    scandir=os.scandir
    def recorded_read(path,*args,**kwargs):
        try:
            content=read(path,*args,**kwargs)
        except OSError as exc:
            events.append(dict(kind='read',path=str(path),errno=exc.errno,error=str(exc)))
            raise
        events.append(dict(kind='read',path=str(path),content=content,errno=0,**digest(content.encode())))
        return content
    def recorded_run(args,*pos,**kwargs):
        if ACTIVE_GUARD: ACTIVE_GUARD.check()
        try:
            result=execute(args,*pos,**kwargs)
        except (OSError,subprocess.SubprocessError) as exc:
            events.append(dict(kind='command',command=args,error=str(exc),errno=getattr(exc,'errno',None),exit=getattr(exc,'returncode',None),
                               stdout=getattr(exc,'stdout',None),stderr=getattr(exc,'stderr',None)))
            raise
        events.append(dict(kind='command',command=args,exit=result.returncode,stdout=result.stdout,stderr=result.stderr))
        return result
    @contextlib.contextmanager
    def recorded_scandir(path):
        try:
            with scandir(path) as entries:
                entries=list(entries)
                events.append(dict(kind='scandir',path=str(path),entries=[dict(name=e.name,path=e.path,is_dir=e.is_dir(follow_symlinks=False)) for e in entries]))
                yield iter(entries)
        except OSError as exc:
            events.append(dict(kind='scandir',path=str(path),error=str(exc),errno=exc.errno))
            raise
    start=time.monotonic()
    try:
        Path.read_text=recorded_read
        subprocess.run=recorded_run
        os.scandir=recorded_scandir
        report=api['read_only_admission'](phase=phase)
    finally:
        Path.read_text=read
        subprocess.run=execute
        os.scandir=scandir
        save(phase+'-ordered.json',events)
    save(phase+'-report.json',report)
    save(phase+'-metrics.json',dict(wall_seconds=time.monotonic()-start,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        swap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,
        aggregate_rss_bytes=sum(int(line.split()[2])*1024 for line in (report.get('original_legacy') or {}).get('process_visibility','').splitlines()[1:] if len(line.split())>=3) if report.get('original_legacy') else 'N/A visibility unavailable; not peak',
        print_axioms='N/A'))
    return report

def controls():
    observed=adapter.identity['self_observation']()
    path=Path(observed['path'])
    names=['memory.high','memory.max','memory.current','memory.peak','memory.swap.max','memory.swap.current',
           'memory.events','pids.max','pids.current','cgroup.procs','cgroup.threads','cgroup.events']
    result=dict(path=str(path),pid=os.getpid(),self_observation=observed,values={})
    for name in names:
        try:result['values'][name]=(path/name).read_text()
        except OSError as exc:result['values'][name]=dict(error=str(exc),errno=exc.errno)
    return result

def check_controls(receipt):
    values=receipt['values']
    for name in ('memory.high','memory.max','memory.swap.max','memory.swap.current','pids.max','memory.peak','memory.current','pids.current','memory.events'):
        if not isinstance(values[name],str):raise ValueError('unreadable scope control: '+name)
    for name,expected in [('memory.high',EXPECTED['high']),('memory.max',EXPECTED['cap']),
                          ('memory.swap.max',0),('memory.swap.current',0),('pids.max',64)]:
        if adapter.c.parse_number(values[name])!=expected:raise ValueError('scope control drift: '+name)
    if adapter.c.parse_number(values['memory.peak'])>EXPECTED['cap']:raise ValueError('scope peak exceeds cap')
    if adapter.c.parse_number(values['memory.current'])>EXPECTED['cap']:raise ValueError('scope current exceeds cap')
    if adapter.c.parse_number(values['pids.current'])>64:raise ValueError('scope task cap exceeded')
    events=adapter.c.pairs(values['memory.events'])
    for key in ('high','max','oom','oom_kill','oom_group_kill'):
        if events[key]!=0:raise ValueError('scope pressure event: '+key)
    return True
