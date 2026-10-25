"""Source-only future fixed metadata producer. Public entry always disabled."""
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import time

HERE=Path(__file__).resolve().parent
STAGE=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate')
PACKET=STAGE/'FinalNativeGate-setup-packet'
UNIT='FinalNativeGate-pin-setup'
TRANSPORT_SECONDS=120
SUMMARY_LIMIT=4*2**20


def main():
    print('FinalNativeGate setup source-only: disabled; review and new allocation required')
    return 78


def _inputs():
    from FinalNativeGate_seal import PLAN_SHA256
    with (HERE/'FinalNativeGate-plan.json').open('rb') as stream:raw=stream.read(SUMMARY_LIMIT+1)
    if len(raw)>SUMMARY_LIMIT or hashlib.sha256(raw).hexdigest()!=PLAN_SHA256:raise ValueError('setup plan seal/size')
    return json.loads(raw)


def _publish(name,value):
    # Fixed exclusive own packet, bounded streaming JSON, durable data only.
    path=PACKET/name;h=hashlib.sha256();size=0
    with path.open('xb') as out:
        for piece in json.JSONEncoder(sort_keys=True).iterencode(value):
            raw=piece.encode();size+=len(raw)
            if size>512*2**20:raise ValueError('metadata record512MiB ceiling')
            out.write(raw);h.update(raw)
        out.flush();os.fsync(out.fileno())
    fd=os.open(PACKET,os.O_DIRECTORY|os.O_RDONLY|os.O_NOFOLLOW)
    try:os.fsync(fd)
    finally:os.close(fd)
    return dict(name=name,size=size,sha256=h.hexdigest())


def _guard():
    from FinalNativeGate_guard import Guard
    class MetadataGuard(Guard):
        budget=512*2**20
        max_samples=6000  #120s /20ms; sampled RSS, no continuous-memory theorem
    return MetadataGuard()


def _prospective():
    # Private future orchestration, still unreachable from main. New allocation
    # and review required;120s timeout is transport,115s alarm is inside collection.
    if HERE!=STAGE:raise ValueError('wrong fixed setup stage')
    import datetime,fcntl,subprocess,zoneinfo
    import FinalNativeGate_setup_observe as observation
    from FinalNativeGate_cleanup import cleanup
    from FinalNativeGate import _cancel_child
    from FinalNativeGate_guard import Proc
    PACKET.mkdir(mode=0o700,exist_ok=False)
    p=_inputs();guard=_guard();child=None;fd=None;ident=None;errors=[];failed=True
    signal.signal(signal.SIGUSR1,lambda *_: (_ for _ in ()).throw(RuntimeError('metadata guard failed')))
    hm=datetime.datetime.now(zoneinfo.ZoneInfo('Europe/London')).strftime('%H%M')
    with open('/tmp/aspis-r0-lean.lock','r') as lock:
        if not (hm>='2230' or hm<'1400'):fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        try:
            guard.start();observation.ACTIVE_GUARD=guard
            report=observation.collect('prospective')
            if report['decision']['allowed'] is not True:raise ValueError('setup prospective admission denied')
            # Data recipe only; missing clean fixed environment is a hard blocker.
            env=p['setup_environment']
            if not env:raise ValueError('missing reviewed clean setup environment')
            argv=['/usr/bin/systemd-run','--user','--scope','--unit='+UNIT,
                '-p','MemoryHigh=768M','-p','MemoryMax=1G','-p','MemorySwapMax=0','-p','TasksMax=64',
                '/usr/bin/timeout','120','/usr/bin/python3','-I','-B',str(STAGE/'FinalNativeGate_setup_inside.py')]
            _publish('FinalNativeGate-setup-argv.json',argv)
            with (PACKET/'FinalNativeGate-setup.stdout').open('xb') as out,(PACKET/'FinalNativeGate-setup.stderr').open('xb') as err:
                child=subprocess.Popen(argv,cwd=STAGE,env=env,stdout=out,stderr=err)
                fd=os.pidfd_open(child.pid);ident=Proc().identity(child.pid);guard.remember(ident,os.getpid())
                deadline=time.monotonic()+120
                while child.returncode is None:
                    guard.check();pid,status,_=os.wait4(child.pid,os.WNOHANG)
                    if pid:child.returncode=os.waitstatus_to_exitcode(status);break
                    if time.monotonic()>deadline:raise TimeoutError('setup120s transport')
                    time.sleep(.05)
                failed=child.returncode!=0
        except BaseException as exc:errors.append(repr(exc))
        finally:
            signal.signal(signal.SIGUSR1,signal.SIG_IGN)
            closure=cleanup(child,fd,ident,guard,_cancel_child);errors.extend(closure['errors'])
            observation.ACTIVE_GUARD=None
            _publish('FinalNativeGate-setup-parent-terminal.json',dict(failed=failed or bool(errors),errors=errors,
                unresolved=closure['unresolved'],guard=closure['monitor'],print_axioms='N/A',execution_authority=False))
    return 78 if failed or errors else 0


def _collect():
    # Future inside-only body. No mkdir/cache mutation, native probe or compiler.
    if HERE!=STAGE:raise ValueError('wrong fixed setup stage')
    from FinalNativeGate_guard import inherited_limits,check_limits
    import FinalNativeGate_setup_observe as observation
    from FinalNativeGate_catalog import discover
    from FinalNativeGate_bounded import Reader
    from FinalNativeGate_elf import dependencies
    p=_inputs();guard=_guard();initial=inherited_limits();check_limits(initial)
    failed=True;errors=[];data=[];start=time.monotonic();deadline=start+115
    signal.signal(signal.SIGUSR1,lambda *_: (_ for _ in ()).throw(RuntimeError('metadata resident guard failed')))
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('metadata115s alarm')))
    signal.alarm(115);observation.ACTIVE_GUARD=guard
    try:
        guard.start()
        # Entire numerical policy and visibility/scans retained by separate1G adapter.
        for phase in ('inside-scope','go'):
            report=observation.collect(phase)
            if report['decision']['allowed'] is not True:raise ValueError('metadata admission denied')
            control=observation.controls();observation.check_controls(control)
            if Path(control['path']).name!=UNIT+'.scope':raise ValueError('setup actual unit drift')
            data.append(_publish('FinalNativeGate-setup-'+phase+'-controls.json',control))
        roots=p['setup_catalog_roots'];guard.check()
        catalog,missing=discover(roots,p['historical_MIR']['file_count']+len(p['files'])+len(roots),deadline)
        data.append(_publish('FinalNativeGate-candidate-catalog.json',catalog))
        # Unsafe/unknown aliases never silently followed or certified complete.
        pins={};elf=[];unresolved=list(missing)+[dict(reason=x) for x in p['setup_deferred']]
        if not missing:
            reader=Reader(catalog)
            for path,e in catalog['entries'].items():
                guard.check()
                if time.monotonic()>deadline:raise TimeoutError('metadata deadline')
                if e['kind']!='file':continue
                pins[path]=reader.pin(path)
                if e['mode']&0o111 or '.so' in Path(path).name:
                    item=dependencies(reader,path);elf.append(item)
                    if item['format']!='ELF64LE' or item.get('search'):
                        unresolved.append(dict(path=path,reason='script/archive or ELF search requires explicit reviewed role/mapping'))
                    for name in item.get('needed',[]):
                        mapped=p['setup_library_mapping'].get(name)
                        if mapped not in pins and mapped not in catalog['entries']:
                            unresolved.append(dict(path=path,needed=name,proposal=[str(Path(d)/name) for d in p['setup_library_search']]))
                    for loader in item.get('interpreter',[]):
                        if loader not in catalog['entries']:unresolved.append(dict(path=path,interpreter=loader))
            data.append(_publish('FinalNativeGate-candidate-pins.json',pins))
            data.append(_publish('FinalNativeGate-candidate-elf.json',elf))
        data.append(_publish('FinalNativeGate-candidate-environment-limits.json',dict(environment=dict(os.environ),limits=initial)))
        check_limits(inherited_limits(),initial);guard.check()
        data.append(_publish('FinalNativeGate-unresolved.json',unresolved))
        # This step supplies data, never seals or updates the execution plan.
        failed=bool(unresolved)
    except BaseException as exc:errors.append(repr(exc))
    finally:
        signal.signal(signal.SIGUSR1,signal.SIG_IGN)
        try:monitor=guard.finish(failed=failed)
        except BaseException as exc:monitor=None;errors.append('guard finish: '+repr(exc))
        observation.ACTIVE_GUARD=None
        try:data.append(_publish('FinalNativeGate-setup-guard.json',monitor))
        except BaseException as exc:errors.append('guard receipt: '+repr(exc))
        u=resource.getrusage(resource.RUSAGE_SELF)
        summary=dict(status='UNREADY' if failed or errors else 'DATA_PENDING_LEAD_REVIEW',errors=errors,data=data,
                     wall_seconds=time.monotonic()-start,peak_rss=u.ru_maxrss,swaps=u.ru_nswap,
                     print_axioms='N/A',execution_authority=False,source_revision=p['source_revision'])
        if len(json.dumps(summary).encode())>SUMMARY_LIMIT:raise ValueError('public4MiB summary ceiling')
        _publish('FinalNativeGate-setup-terminal.json',summary)
        signal.alarm(0)
    return 78 if failed or errors else 0


if __name__=='__main__':
    raise SystemExit(main())
