"""Reviewed observation functions; concrete collector, no marker/GO callback."""
import contextlib, hashlib, json, os, resource, shutil, stat, struct, subprocess, sys, sysconfig, time
from pathlib import Path
import FinalNativeGate_setup_adapter as adapter
HERE=Path(__file__).resolve().parent
EXPECTED=dict(high=768*2**20, cap=2**30, swap_max=0, tasks_max=64)
ACTIVE_GUARD=None

def save(name,value):
    # Fixed exclusive own packet. Large derived JSON stays external; receipts
    # carry size/hash only. Streaming serialization has a64MiB disk ceiling.
    packet=HERE/'FinalNativeGate-setup-packet'
    owned=packet.lstat()
    if not stat.S_ISDIR(owned.st_mode) or owned.st_uid!=os.getuid() or owned.st_mode&0o077:raise ValueError('private owned packet required')
    h=hashlib.sha256();size=0
    with (packet/name).open('xb') as out:
        for piece in json.JSONEncoder(sort_keys=True).iterencode(value):
            raw=piece.encode();size+=len(raw)
            if size>64*2**20:raise ValueError('raw derived JSON64MiB disk bound')
            out.write(raw);h.update(raw)
        out.flush();os.fsync(out.fileno())
    fd=os.open(packet,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try:os.fsync(fd)
    finally:os.close(fd)
    return dict(name=name,size=size,sha256=h.hexdigest())

def digest(data):
    return dict(sha256=hashlib.sha256(data).hexdigest(), size=len(data))

def filepin(path,catalog):
    from FinalNativeGate_bounded import Reader
    return Reader(catalog).pin(path)


def runtime_pins(catalog):
    # Changed helper semantics: finite reviewed runtime catalog, no sys.path
    # forest walk, PATH discovery or whole-file ELF read. Missing data denies.
    from FinalNativeGate_bounded import Reader
    if sys.executable!=catalog['python_executable'] or sysconfig.get_path('stdlib')!=catalog['stdlib']:
        raise ValueError('Python executable/stdlib role drift')
    for name,path in catalog['tools'].items():
        if shutil.which(name)!=path:raise ValueError('PATH tool resolution drift: '+name)
    limit=catalog['maps_limit']
    if type(limit) is not int or limit<=0:raise ValueError('missing finite maps bound')
    with open('/proc/self/maps') as stream:raw=stream.read(limit+1)
    if len(raw)>limit:raise ValueError('maps bound')
    mapped=set()
    for line in raw.splitlines():
        parts=line.split(None,5)
        if len(parts)==6 and parts[5].startswith('/'):
            if parts[5].endswith(' (deleted)'):raise ValueError('deleted runtime mapping')
            mapped.add(parts[5])
    if mapped!=set(catalog['mapped_libraries']):raise ValueError('runtime mapping catalog drift')
    pins=Reader(catalog).inventory(catalog['roots'])
    if not mapped.issubset(pins) or not set(catalog['tools'].values()).issubset(pins):
        raise ValueError('runtime/tool catalog coverage gap')
    return dict(executable=sys.executable,version=sys.version,files=pins,tools=catalog['tools'],mapped_libraries=sorted(mapped))


def collect(phase):
    """Record every ordered filesystem/command input without changing API logic."""
    api=adapter.__dict__
    events=[];raw_bytes=0;event_limit=32768;raw_limit=16*2**20
    def append(event):
        nonlocal raw_bytes
        raw_bytes+=len(json.dumps(event).encode())
        if len(events)>=event_limit or raw_bytes>raw_limit:raise ValueError('raw visibility32768 event/16MiB bound')
        events.append(event)
    read=Path.read_text
    execute=subprocess.run
    scandir=os.scandir
    def recorded_read(path,*args,**kwargs):
        try:
            # Kernel pseudo-files have no useful stat size; finite streaming read.
            with path.open('r',*args,**kwargs) as stream:content=stream.read(4*2**20+1)
            if len(content)>4*2**20:raise ValueError('raw visibility per-read4MiB bound')
        except OSError as exc:
            append(dict(kind='read',path=str(path),errno=exc.errno,error=str(exc)))
            raise
        append(dict(kind='read',path=str(path),content=content,errno=0,**digest(content.encode())))
        return content
    def recorded_run(args,*pos,**kwargs):
        if ACTIVE_GUARD: ACTIVE_GUARD.check()
        try:
            from FinalNativeGate_scope import command
            if pos or kwargs.get('input') is not None:raise ValueError('unexpected metadata command input')
            result=command(args,timeout=kwargs.get('timeout',15),limit=4*2**20,record=True)
        except (OSError,ValueError,subprocess.SubprocessError) as exc:
            append(dict(kind='command',command=args,error=str(exc),errno=getattr(exc,'errno',None),exit=getattr(exc,'returncode',None),
                               stdout=getattr(exc,'stdout',None),stderr=getattr(exc,'stderr',None)))
            raise
        append(dict(kind='command',command=args,exit=result.returncode,stdout=result.stdout,stderr=result.stderr))
        return result
    @contextlib.contextmanager
    def recorded_scandir(path):
        try:
            with scandir(path) as entries:
                bounded_entries=[]
                for entry in entries:
                    if len(bounded_entries)>=32768:raise ValueError('raw scandir entry bound')
                    bounded_entries.append(entry)
                entries=bounded_entries
                append(dict(kind='scandir',path=str(path),entries=[dict(name=e.name,path=e.path,is_dir=e.is_dir(follow_symlinks=False)) for e in entries]))
                yield iter(entries)
        except OSError as exc:
            append(dict(kind='scandir',path=str(path),error=str(exc),errno=exc.errno))
            raise
    start=time.monotonic()
    try:
        Path.read_text=recorded_read
        subprocess.run=recorded_run
        os.scandir=recorded_scandir
        report=api['read_only_admission'](phase='inside-scope' if phase=='go' else phase)
    finally:
        Path.read_text=read
        subprocess.run=execute
        os.scandir=scandir
        ordered=save(phase+'-ordered.json',events)
    report['raw_receipts']=[ordered]
    report_receipt=save(phase+'-report.json',report)
    metrics_receipt=save(phase+'-metrics.json',dict(wall_seconds=time.monotonic()-start,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        swap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,
        aggregate_rss_bytes=sum(int(line.split()[2])*1024 for line in (report.get('original_legacy') or {}).get('process_visibility','').splitlines()[1:] if len(line.split())>=3) if report.get('original_legacy') else 'N/A visibility unavailable; not peak',
        print_axioms='N/A'))
    report['raw_receipts'].extend([report_receipt,metrics_receipt])
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
    # DATA only, not an added permission gate or a cancellation probe.
    # Kernel/cgroup delegation can still refuse an apparently writable control.
    try:
        fd=os.open(path,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        try:
            s=os.stat('cgroup.kill',dir_fd=fd,follow_symlinks=False)
            result['cleanup_control_metadata']=dict(uid=s.st_uid,gid=s.st_gid,mode=s.st_mode,
                regular=stat.S_ISREG(s.st_mode),euid=os.geteuid(),egid=os.getegid(),groups=os.getgroups(),
                effective_write_access=os.access('cgroup.kill',os.W_OK,dir_fd=fd,effective_ids=True,follow_symlinks=False),
                kernel_write_viability='UNOBSERVED; metadata only; review before final Kani charge')
        finally:os.close(fd)
    except (OSError,NotImplementedError) as exc:
        result['cleanup_control_metadata']=dict(error=repr(exc),kernel_write_viability='UNRESOLVED')
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
