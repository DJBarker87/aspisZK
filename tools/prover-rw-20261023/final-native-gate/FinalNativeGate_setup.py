"""Source-only future fixed metadata producer. Public entry always disabled."""
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import stat
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
    with (HERE/'FinalNativeGate-plan.json').open('rb') as stream:
        before=os.fstat(stream.fileno())
        if before.st_size>SUMMARY_LIMIT:raise ValueError('setup plan stat bound')
        raw=stream.read(SUMMARY_LIMIT+1)
        if before!=os.fstat(stream.fileno()):raise ValueError('setup plan identity drift')
    if len(raw)>SUMMARY_LIMIT or hashlib.sha256(raw).hexdigest()!=PLAN_SHA256:raise ValueError('setup plan seal/size')
    return json.loads(raw)


def _publish(name,value):
    # Fixed exclusive own packet, bounded streaming JSON, durable data only.
    owned=PACKET.lstat()
    if not stat.S_ISDIR(owned.st_mode) or owned.st_uid!=os.getuid() or owned.st_mode&0o077:raise ValueError('owned private setup packet required')
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
    from FinalNativeGate_scope import FixedScope,environment
    from FinalNativeGate_candidate import bootstrap,stable
    PACKET.mkdir(mode=0o700,exist_ok=False)
    p=_inputs();guard=_guard();child=None;fd=None;ident=None;errors=[];failed=True
    scope=FixedScope('setup')
    signal.signal(signal.SIGUSR1,lambda *_: (_ for _ in ()).throw(RuntimeError('metadata guard failed')))
    hm=datetime.datetime.now(zoneinfo.ZoneInfo('Europe/London')).strftime('%H%M')
    with open('/tmp/aspis-r0-lean.lock','r') as lock:
        if not (hm>='2230' or hm<'1400'):fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        try:
            guard.start();observation.ACTIVE_GUARD=guard
            report=observation.collect('prospective')
            if report['decision']['allowed'] is not True:raise ValueError('setup prospective admission denied')
            parent_bootstrap=bootstrap(STAGE)
            env=environment()  # concrete proposal; UID/bus are candidate DATA
            scope.preflight();argv=scope.argv(env)
            _publish('FinalNativeGate-setup-argv.json',argv)
            with (PACKET/'FinalNativeGate-setup.stdout').open('xb') as out,(PACKET/'FinalNativeGate-setup.stderr').open('xb') as err:
                deadline=time.monotonic()+120
                child=subprocess.Popen(argv,cwd=STAGE,env=env,stdout=out,stderr=err)
                fd=os.pidfd_open(child.pid);ident=Proc().identity(child.pid);guard.remember(ident,os.getpid())
                scope.bind_release(child,ident,guard)
                while child.returncode is None:
                    guard.check();pid,status,_=os.wait4(child.pid,os.WNOHANG)
                    if pid:child.returncode=os.waitstatus_to_exitcode(status);break
                    if time.monotonic()>deadline:raise TimeoutError('setup120s transport')
                    time.sleep(.05)
                failed=child.returncode!=0
                stable(parent_bootstrap,bootstrap(STAGE))
        except BaseException as exc:errors.append(repr(exc))
        finally:
            signal.signal(signal.SIGUSR1,signal.SIG_IGN)
            closure=cleanup(child,fd,ident,guard,_cancel_child,scope,outer=True);errors.extend(closure['errors'])
            observation.ACTIVE_GUARD=None
            for name,value in [('FinalNativeGate-setup-parent-cleanup.json',closure),
                               ('FinalNativeGate-setup-parent-guard.json',closure['monitor']),
                               ('FinalNativeGate-setup-parent-terminal.json',dict(failed=failed or bool(errors),errors=errors,
                                unresolved=closure['unresolved'],print_axioms='N/A',execution_authority=False))]:
                try:_publish(name,value)
                except BaseException as exc:errors.append('terminal write '+name+': '+repr(exc))

    return 78 if failed or errors else 0


def _collect():
    # Future inside-only body. No mkdir/cache mutation, native probe or compiler.
    if HERE!=STAGE:raise ValueError('wrong fixed setup stage')
    from FinalNativeGate_guard import inherited_limits,check_limits
    import FinalNativeGate_setup_observe as observation
    from FinalNativeGate_candidate import Acquisition,bootstrap,stable,runtime_proposal,verify_expected,data_status
    from FinalNativeGate_scope import environment
    from FinalNativeGate_bounded import Reader
    from FinalNativeGate_elf import dependencies
    p=_inputs();guard=_guard();initial=inherited_limits();check_limits(initial)
    acquisition=None;failed=True;errors=[];data=[];unresolved=[];start=time.monotonic();deadline=start+115
    signal.signal(signal.SIGUSR1,lambda *_: (_ for _ in ()).throw(RuntimeError('metadata resident guard failed')))
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('metadata115s alarm')))
    signal.alarm(115);observation.ACTIVE_GUARD=guard
    try:
        guard.start()
        boot_before=bootstrap(STAGE)
        runtime=runtime_proposal()
        acquisition=Acquisition(deadline)
        proposal=environment()
        acquisition.add(proposal['XDG_RUNTIME_DIR'])
        acquisition.add(proposal['XDG_RUNTIME_DIR']+'/bus')
        # Exact planned files, native/sysroot roots, Python stdlib + mapped objects.
        # No MIR dump/target forest. Native directory aliases below roots are DATA.
        for path in sorted(p['files']):acquisition.add(path)
        for path in p['native_roots']:acquisition.add(path,recurse=True)
        for path in (runtime['executable'],*runtime['mapped_libraries']):acquisition.add(path)
        acquisition.add(runtime['stdlib'],recurse=True)
        # Only Cargo fingerprint metadata, never artifacts or a50077-file MIR walk.
        cache_proposals=[]
        base='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/'
        for target,profile in [('resume-p6/compact/target','debug'),('resume-mir/target','release')]:
            root=base+target
            acquisition.add(root)
            acquisition.add(root+'/'+profile)
            acquisition.add(root+'/'+profile+'/.fingerprint',recurse=True)
            cache_proposals.append(dict(target=root,profile=profile,compatibility='UNREVIEWED',selected=False))
        # ELF dependency names are metadata; finite explicit search proposals can
        # be acquired without invoking loader/compiler/ldd. No closure approval.
        elf=[]
        for path in sorted(acquisition.files):
            e=acquisition.rows.get(path)
            if e is None or e['kind']=='link' or e['mode']&0o111 or '.so' in Path(path).name:
                item=dependencies(Reader(acquisition.catalog()),path);elf.append(item)
                for loader in item.get('interpreter',[]):acquisition.add(loader)
                for name in item.get('needed',[]):
                    if '/' in name:
                        acquisition.unresolved.append(dict(path=path,needed=name,reason='non-basename ELF role'))
                    else:
                        for directory in p['setup_library_search']:acquisition.add(str(Path(directory)/name))
                if item['format']!='ELF64LE' or item.get('search'):
                    acquisition.unresolved.append(dict(path=path,reason='native/script/search role requires review'))
        before=acquisition.snapshot();verify_expected(before,p['files'])
        # Source/native hashes, stamps, chains all span BOTH full admission scans
        # and ELF/runtime/data assembly, rather than merely one individual read.
        controls=[]
        for phase in ('inside-scope','go'):
            report=observation.collect(phase)
            if report['decision']['allowed'] is not True:raise ValueError('metadata admission denied')
            control=observation.controls();observation.check_controls(control)
            if Path(control['path']).name!=UNIT+'.scope':raise ValueError('setup actual unit drift')
            controls.append(dict(phase=phase,control=control,raw_receipts=report.get('raw_receipts',[])))
        unresolved=acquisition.unresolved+[
            dict(reason='native tool/loader/sysroot dependency closure needs lead role review'),
            dict(reason='candidate runtime/bus/UID/environment and cache compatibility need review')]
        after=acquisition.snapshot();stable(before,after)
        runtime_after=runtime_proposal()
        stable({k:v for k,v in runtime.items() if k!='maps'},
               {k:v for k,v in runtime_after.items() if k!='maps'})
        runtime['maps_after']=runtime_after['maps']  # anonymous heap growth is DATA
        stable(boot_before,bootstrap(STAGE))
        check_limits(inherited_limits(),initial);guard.check()
        for name,value in [('catalog',after),('elf',elf),('runtime',runtime),('controls',controls),
                           ('cache-proposals',cache_proposals),('bootstrap',boot_before),
                           ('environment-limits',dict(environment=dict(os.environ),proposal=environment(),limits=initial)),
                           ('unresolved',unresolved)]:
            data.append(_publish('FinalNativeGate-candidate-'+name+'.json',value))
        # Unknown roles are the requested DATA, not a failed executable gate.
        failed=False
    except BaseException as exc:
        errors.append(repr(exc))
        if acquisition is not None:
            try:data.append(_publish('FinalNativeGate-candidate-partial-failure.json',dict(catalog=acquisition.catalog(),unresolved=acquisition.unresolved,error=repr(exc))))
            except BaseException as write_error:errors.append('partial failure receipt: '+repr(write_error))
    finally:
        signal.signal(signal.SIGUSR1,signal.SIG_IGN)
        try:monitor=guard.finish(failed=failed)
        except BaseException as exc:monitor=None;errors.append('guard finish: '+repr(exc))
        try:guard.check()
        except BaseException as exc:errors.append('guard final check: '+repr(exc))
        if monitor and monitor.get('error'):errors.append('guard: '+str(monitor['error']))
        observation.ACTIVE_GUARD=None
        try:data.append(_publish('FinalNativeGate-setup-guard.json',monitor))
        except BaseException as exc:errors.append('guard receipt: '+repr(exc))
        u=resource.getrusage(resource.RUSAGE_SELF)
        summary=dict(status=data_status(unresolved,errors or (['collection incomplete'] if failed else [])),errors=errors,data=data,
                     wall_seconds=time.monotonic()-start,peak_rss=u.ru_maxrss,swaps=u.ru_nswap,
                     print_axioms='N/A',execution_authority=False,source_revision=p['source_revision'])
        if len(json.dumps(summary).encode())>SUMMARY_LIMIT:raise ValueError('public4MiB summary ceiling')
        try:_publish('FinalNativeGate-setup-terminal.json',summary)
        finally:signal.alarm(0)
    return 78 if failed or errors else 0


if __name__=='__main__':
    raise SystemExit(main())
