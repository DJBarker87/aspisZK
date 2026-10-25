"""Metadata-only one-shot host runner. No compiler, consumer, or allocation probe."""
import contextlib
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import runpy
import shutil
import signal
import subprocess
import struct
import sys
import sysconfig
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import ResourceRssGOv3_adapter as adapter
from ResourceRssGOv3_guard import Guard, GuardError, inherited_limits, check_limits
ACTIVE_GUARD = None
EXPECTED = dict(high=3*2**30, cap=4*2**30, swap_max=0, tasks_max=64)
UNIT = 'resource-rss-go-v3-20261025'
EPOCH = 'ResourceRssGOv3-20261025-epoch1'
STAGE = '/home/dombarker/project-offloads/codex-cx-resource-rss-go-v3-20261025'
ENV_BINARY = '/usr/bin/env'
PYTHON_BINARY = '/usr/bin/python3'
LOCK = '/tmp/aspis-r0-lean.lock'
MODE = 'limited ResourceStability20261025-v1 policy; one metadata epoch only; no consumer'
ENV_KEYS = {'HOME','USER','LOGNAME','PATH','LANG','XDG_RUNTIME_DIR','DBUS_SESSION_BUS_ADDRESS'}


def digest(data):
    return dict(sha256=hashlib.sha256(data).hexdigest(), size=len(data))


def filepin(path):
    return digest(Path(path).read_bytes())


def runtime_pins():
    # Pure ELF metadata inspection: no ldd/native helper execution. Reject new
    # env runtime dependencies rather than silently leaving them unpinned.
    raw=Path('/usr/bin/env').read_bytes()
    if raw[:6] != b'\x7fELF\x02\x01' or struct.unpack_from('<H',raw,18)[0] != 62:
        raise ValueError('env ELF ABI drift')
    phoff,shoff=struct.unpack_from('<QQ',raw,32)
    phsize,phnum,shsize,shnum=struct.unpack_from('<HHHH',raw,54)
    interp=[]
    for i in range(phnum):
        ph=struct.unpack_from('<IIQQQQQQ',raw,phoff+i*phsize)
        if ph[0]==3:interp.append(raw[ph[2]:ph[2]+ph[5]].rstrip(b'\0').decode())
    sections=[struct.unpack_from('<IIQQQQIIQQ',raw,shoff+i*shsize) for i in range(shnum)]
    needed=[]
    for section in sections:
        if section[1]!=6:continue
        strings=sections[section[6]]
        table=raw[strings[4]:strings[4]+strings[5]]
        for off in range(section[4],section[4]+section[5],section[9]):
            tag,value=struct.unpack_from('<qQ',raw,off)
            if tag==1:needed.append(table[value:].split(b'\0',1)[0].decode())
            if tag in (15,29):raise ValueError('env ELF search path drift')
    if interp!=['/lib64/ld-linux-x86-64.so.2'] or needed!=['libc.so.6']:
        raise ValueError('env ELF runtime dependency drift')
    std = Path(sysconfig.get_path('stdlib')).resolve()
    files = {}
    for root, dirs, names in os.walk(std):
        dirs[:] = sorted(d for d in dirs if d not in ('site-packages','dist-packages','__pycache__'))
        for name in sorted(names):
            if name.endswith(('.py','.so')):
                p = Path(root)/name
                files[str(p)] = filepin(p)
    mapped = {}
    for line in Path('/proc/self/maps').read_text().splitlines():
        parts = line.split(None,5)
        if len(parts)==6 and parts[5].startswith('/'):
            p=parts[5]
            mapped[p]=filepin(p)
    tools = {name:dict(path=shutil.which(name), **filepin(shutil.which(name)))
             for name in ('ps','systemctl','docker','systemd-run')}
    return dict(executable=str(Path(sys.executable).resolve()), executable_pin=filepin(sys.executable),
                version=sys.version, stdlib=files, mapped_libraries=mapped, tools=tools,
                env_binary=dict(path='/usr/bin/env', **filepin('/usr/bin/env')),
                env_elf_contract=dict(interpreter=interp,needed=needed),
                env_dependencies={p:filepin(p) for p in ('/lib64/ld-linux-x86-64.so.2', '/lib/x86_64-linux-gnu/libc.so.6')})


def save(name, value):
    # All raw captures stay intact on the host. Local export applies size policy.
    p=HERE/'capture'/name
    p.parent.mkdir(exist_ok=True)
    with p.open('x') as out:
        json.dump(value,out,sort_keys=True,indent=2)
        out.write('\n')


def verify_environment(expected):
    if set(expected) != ENV_KEYS or dict(os.environ) != expected:
        # Only names and expected-key observed-value digests; never dirty values.
        detail=dict(missing_keys=sorted(ENV_KEYS-set(os.environ)),
                    unexpected_keys=sorted(set(os.environ)-ENV_KEYS),
                    expected_key_value_digests={k:digest(os.environ[k].encode()) if k in os.environ else None for k in sorted(ENV_KEYS)})
        raise ValueError('environment differs from allowlist pin: '+json.dumps(detail,sort_keys=True))


def verify(manifest):
    if manifest.get('epoch') != EPOCH or manifest.get('stage') != STAGE or str(HERE) != STAGE:
        raise ValueError('epoch/stage pin drift')
    if manifest.get('scope_argv') != scope_argv(manifest):
        raise ValueError('literal scope argv pin drift')
    if manifest.get('mode') != MODE:raise ValueError('mode pin drift')
    actual={name:filepin(HERE/name) for name in manifest['files']}
    if actual != manifest['files']:
        raise ValueError('source drift')
    check_limits(inherited_limits(), manifest['inherited_limits'])
    runtime=runtime_pins()
    if runtime != manifest['runtime']:
        raise ValueError('runtime/dependency drift')
    verify_environment(manifest['env'])
    return dict(files=actual,runtime=runtime,env=dict(os.environ),mode=MODE)


def scope_argv(manifest):
    if set(manifest['env']) != ENV_KEYS:raise ValueError('invalid pinned env keys')
    return ['/usr/bin/systemd-run','--user','--scope','--unit='+UNIT,
            '-p','MemoryHigh=3G','-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64',
            ENV_BINARY,'-i']+[k+'='+v for k,v in sorted(manifest['env'].items())]+[
            PYTHON_BINARY,'-I','-B',STAGE+'/ResourceRssGOv3_host.py','go']


def flow(prospective, launch):
    report=prospective()
    if report['decision']['allowed'] is not True:
        return dict(terminal='PROSPECTIVE_DENY', prospective_exit=78, scope_created=False)
    return launch()


def go_flow(report, marker):
    if report['decision']['allowed'] is not True:
        return dict(terminal='GO_DENY', go_exit=78, marker_exit=None)
    marker()
    return dict(terminal='GO_MARKER_PASS', go_exit=0, marker_exit=0)


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


def main():
    action=sys.argv[1]
    manifest=json.loads((HERE/'ResourceRssGOv3_manifest.json').read_text())
    start=time.monotonic()
    save(action+'-pre-pins.json',verify(manifest))
    if action=='run':
        with (HERE/'ResourceRssGOv3_ATTEMPTED').open('x') as sentinel:
            sentinel.write(EPOCH+'; new epoch 1/1; prior three epochs remain charged failures; fixed Q4GiB; transport/observation failures terminal'+chr(10))
    if action=='go':
        before_controls=controls()
        save('go-controls-before.json',before_controls)
        report=collect('inside-scope')
        save('go-pins.json',verify(manifest))
        def marker():
            ACTIVE_GUARD.check()
            # No subprocess or workload: only actual identity, after GO.
            save('marker.json',dict(pid=os.getpid(),cgroup=Path('/proc/self/cgroup').read_text(),identity='ResourceRssGOv3 metadata marker only',self_observation=adapter.identity['self_observation'](),go_report_pin=filepin(HERE/'capture/inside-scope-report.json'),source_manifest_pin=filepin(HERE/'ResourceRssGOv3_manifest.json')))
        after_controls=controls()
        save('go-controls-after-scan.json',after_controls)
        gated=report
        try:
            check_controls(before_controls);check_controls(after_controls)
            binding=report['decision']['scope_binding']['self_identity']
            for observed in (before_controls,after_controls):
                if {k:v for k,v in observed['self_observation'].items() if k!='reads'}!=binding:
                    raise ValueError('control/GO process identity drift')
            save('go-control-check.json',dict(allowed=True))
        except (KeyError,TypeError,ValueError) as exc:
            save('go-control-check.json',dict(allowed=False,error=str(exc)))
            gated=dict(decision=dict(allowed=False))
        result=go_flow(gated,marker)
        final_controls=controls()
        save('go-controls-after.json',final_controls)
        check_controls(final_controls)
        code=result['go_exit']
    elif action=='run':
        # One shared lock, same path/flock protocol as immutable manager launchers.
        # Nonblocking: a busy lock is a terminal pre-capture blocker, never a retry.
        with open(LOCK,'r') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            save('lock.json',dict(path=LOCK,mode='LOCK_EX|LOCK_NB',held_through='prospective and scope exit',
                                  inode=os.fstat(lock.fileno()).st_ino))
            def launch():
                ACTIVE_GUARD.check()
                argv=scope_argv(manifest)
                save('scope-argv.json',argv)
                child=subprocess.Popen(argv,stdout=(HERE/'capture/scope.stdout').open('x'),stderr=(HERE/'capture/scope.stderr').open('x'),env=manifest['env'])
                _,status,usage=os.wait4(child.pid,0)
                code=os.waitstatus_to_exitcode(status)
                child.returncode=code
                save('scope-child.json',dict(argv=argv,exit=code,peak_rss_bytes=usage.ru_maxrss*1024,swap=usage.ru_nswap))
                return dict(terminal='SCOPE_EXIT',scope_created=True,scope_runner_exit=code,prospective_exit=0)
            result=flow(lambda:collect('prospective'),launch)
        code=0 if result.get('scope_runner_exit',78)==0 else 78
    else:
        raise ValueError('unknown action')
    save(action+'-post-pins.json',verify(manifest))
    save(action+'-exit.json',dict(**result,exit=code,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        swap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A'))
    return code

def guarded_main():
    global ACTIVE_GUARD
    signal.alarm(115)  # whole metadata diagnostic, including monitor startup/pins
    action=sys.argv[1]
    initial=inherited_limits()
    save(action+'-inherited-limits-initial.json',initial)
    check_limits(initial)
    manifest=json.loads((HERE/'ResourceRssGOv3_manifest.json').read_text())
    check_limits(initial,manifest['inherited_limits'])
    def stop_on_guard(signum, frame):
        raise GuardError('resident watchdog failed; see guard receipt')
    signal.signal(signal.SIGUSR1,stop_on_guard)
    signal.signal(signal.SIGALRM,lambda signum,frame: (_ for _ in ()).throw(GuardError('overall metadata deadline')))
    ACTIVE_GUARD=Guard()
    failed=True
    try:
        ACTIVE_GUARD.start()
        result=main()
        ACTIVE_GUARD.check()
        check_limits(inherited_limits(),initial)
        failed=False
        return result
    finally:
        # Thread survives final collection, child exits and main's exit receipt.
        signal.signal(signal.SIGUSR1,signal.SIG_IGN)
        receipt=ACTIVE_GUARD.finish(failed=failed)
        save(action+'-resident-guard.json',receipt)
        save(action+'-inherited-limits-final.json',inherited_limits())
        ACTIVE_GUARD.check()

if __name__=='__main__':
    raise SystemExit(guarded_main())
