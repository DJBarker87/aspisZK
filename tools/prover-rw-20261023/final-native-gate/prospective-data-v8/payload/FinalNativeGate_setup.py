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
STAGE=Path('/home/dombarker/final-native-gate-v8-20261025')
PACKET=STAGE/'FinalNativeGate-setup-packet'
UNIT='FinalNativeGate-pin-setup'
TRANSPORT_SECONDS=120
SUMMARY_LIMIT=4*2**20


def main():
    import sys
    if HERE!=STAGE:raise ValueError('wrong fixed DATA stage')
    sys.path.insert(0,str(STAGE))
    return _prospective()


def _inputs():
    from FinalNativeGate_bounded import stamp
    from FinalNativeGate_seal import PLAN_SHA256
    with (HERE/'FinalNativeGate-plan.json').open('rb') as stream:
        before=os.fstat(stream.fileno())
        if before.st_size>SUMMARY_LIMIT:raise ValueError('setup plan stat bound')
        raw=stream.read(SUMMARY_LIMIT+1)
        if stamp(before)!=stamp(os.fstat(stream.fileno())):raise ValueError('setup plan identity drift')
    if len(raw)>SUMMARY_LIMIT or hashlib.sha256(raw).hexdigest()!=PLAN_SHA256:raise ValueError('setup plan seal/size')
    return json.loads(raw)


def _publish(name,value,*,limit=512*2**20):
    # Exclusive relative publication in the existing private packet. Never repair,
    # adopt, unlink, rename or chmod an existing or partially written entry.
    if not isinstance(name,str) or not name or name in ('.','..') or '/' in name or '\x00' in name:
        raise ValueError('publication basename required')
    def stamp(s):
        return (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid,s.st_nlink,
                s.st_size,s.st_mtime_ns,s.st_ctime_ns)
    def private_file(s):
        if not stat.S_ISREG(s.st_mode) or s.st_uid!=os.getuid() or s.st_nlink!=1 or stat.S_IMODE(s.st_mode)!=0o600:
            raise ValueError('new publication must be current-owner single-link regular0600')
    owned=PACKET.lstat()
    if not stat.S_ISDIR(owned.st_mode) or owned.st_uid!=os.getuid() or stat.S_IMODE(owned.st_mode)!=0o700:
        raise ValueError('owned private setup packet0700 required')
    directory=os.open(PACKET,os.O_DIRECTORY|os.O_RDONLY|os.O_NOFOLLOW|os.O_CLOEXEC)
    writer=None
    try:
        if stamp(os.fstat(directory))!=stamp(owned):raise ValueError('packet open identity drift')
        writer=os.open(name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600,dir_fd=directory)
        initial=os.fstat(writer);private_file(initial)
        h=hashlib.sha256();size=0
        for piece in json.JSONEncoder(sort_keys=True,allow_nan=False).iterencode(value):
            for offset in range(0,len(piece),16384):
                raw=piece[offset:offset+16384].encode();size+=len(raw)
                if size>limit:raise ValueError('metadata record512MiB ceiling')
                view=memoryview(raw)
                while view:
                    count=os.write(writer,view)
                    if count<=0:raise OSError('publication short write')
                    view=view[count:]
                h.update(raw)
        os.fsync(writer)
        final=os.fstat(writer);private_file(final)
        if (initial.st_dev,initial.st_ino)!=(final.st_dev,final.st_ino) or final.st_size!=size:
            raise ValueError('publication writer identity/size drift')
        if stamp(os.stat(name,dir_fd=directory,follow_symlinks=False))!=stamp(final):
            raise ValueError('publication entry identity drift')
        closing=writer;writer=None;os.close(closing)
        if stamp(os.stat(name,dir_fd=directory,follow_symlinks=False))!=stamp(final):
            raise ValueError('publication closed entry drift')
        # Directory size/times/link count may change from our own new entry
        # (APFS counts files). File nlink remains strictly one above.
        current=os.fstat(directory);entry=PACKET.lstat()
        for s in (current,entry):
            if (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid)!=(owned.st_dev,owned.st_ino,owned.st_mode,owned.st_uid,owned.st_gid):
                raise ValueError('publication packet identity drift')
        os.fsync(directory)
        return dict(name=name,size=size,sha256=h.hexdigest())
    finally:
        try:
            if writer is not None:os.close(writer)
        finally:os.close(directory)


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
    scope=FixedScope('setup');spawn_state='not_started';admission=[]
    signal.signal(signal.SIGUSR1,lambda *_: (_ for _ in ()).throw(RuntimeError('metadata guard failed')))
    hm=datetime.datetime.now(zoneinfo.ZoneInfo('Europe/London')).strftime('%H%M')
    with open('/tmp/aspis-r0-lean.lock','r') as lock:
        if not (hm>='2230' or hm<'1400'):fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        try:
            guard.start();observation.ACTIVE_GUARD=guard
            report=observation.collect('prospective',admission=admission)
            if report['decision']['allowed'] is not True:raise ValueError('setup prospective admission denied')
            parent_bootstrap=bootstrap(STAGE)
            env=environment()  # concrete proposal; UID/bus are candidate DATA
            scope.preflight();argv=scope.argv(env)
            _publish('FinalNativeGate-setup-argv.json',argv)
            with (PACKET/'FinalNativeGate-setup.stdout').open('xb') as out,(PACKET/'FinalNativeGate-setup.stderr').open('xb') as err:
                deadline=time.monotonic()+120
                spawn_state='uncertain'  # Set BEFORE Popen: an exception is not proof of no spawn.
                child=subprocess.Popen(argv,cwd=STAGE,env=env,stdout=out,stderr=err)
                spawn_state='started'
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
            closure=cleanup(child,fd,ident,guard,_cancel_child,scope,outer=True,spawn_state=spawn_state);errors.extend(closure['errors'])
            observation.ACTIVE_GUARD=None
            for name,value in [('FinalNativeGate-setup-parent-cleanup.json',closure),
                               ('FinalNativeGate-setup-parent-guard.json',closure['monitor'])]:
                try:_publish(name,value)
                except BaseException as exc:errors.append('terminal write '+name+': '+repr(exc))
            # Compute only after prior writes: a persisted terminal must include
            # their failures. A terminal write failure still forces nonzero exit.
            terminal=dict(failed=failed or bool(errors) or bool(closure['unresolved']),errors=list(errors),
                          unresolved=closure['unresolved'],admission=admission,spawn_state=spawn_state,print_axioms='N/A',execution_authority=False)
            try:_publish('FinalNativeGate-setup-parent-terminal.json',terminal)
            except BaseException as exc:errors.append('terminal write FinalNativeGate-setup-parent-terminal.json: '+repr(exc))

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
    admission=[];acquisition=None;failed=True;errors=[];data=[];unresolved=[];start=time.monotonic();deadline=start+115
    signal.signal(signal.SIGUSR1,lambda *_: (_ for _ in ()).throw(RuntimeError('metadata resident guard failed')))
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('metadata115s alarm')))
    signal.alarm(115);observation.ACTIVE_GUARD=guard
    try:
        guard.start()
        boot_before=bootstrap(STAGE)
        controls=[]
        report=observation.collect('inside-scope',admission=admission)
        if report['decision']['allowed'] is not True:raise ValueError('metadata inside-scope admission denied')
        control=observation.controls();observation.check_controls(control)
        if Path(control['path']).name!=UNIT+'.scope':raise ValueError('setup actual unit drift')
        controls.append(dict(phase='inside-scope',control=control,raw_receipts=report.get('raw_receipts',[])))
        guard.check()
        acquisition=Acquisition(deadline)
        runtime=runtime_proposal()
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
        missing=sorted(set(p['files'])-acquisition.files)
        if missing:raise ValueError('missing fixed source files: '+json.dumps(missing))
        before=acquisition.snapshot();verify_expected(before,p['files'])
        # Bootstrap covers collection. Acquired metadata/hash interval begins
        # at this snapshot; initial per-entry stamps and known source hashes
        # are checked too. No native hash identity before its first observation.
        report=observation.collect('go',admission=admission)
        if report['decision']['allowed'] is not True:raise ValueError('metadata go admission denied')
        control=observation.controls();observation.check_controls(control)
        if Path(control['path']).name!=UNIT+'.scope':raise ValueError('setup actual unit drift')
        controls.append(dict(phase='go',control=control,raw_receipts=report.get('raw_receipts',[])))
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
        summary=dict(failed=failed or bool(errors),admission=admission,status=data_status(unresolved,errors or (['collection incomplete'] if failed else [])),errors=errors,data=data,
                     wall_seconds=time.monotonic()-start,peak_rss=u.ru_maxrss,swaps=u.ru_nswap,
                     print_axioms='N/A',execution_authority=False,source_revision=p['source_revision'])
        if len(json.dumps(summary).encode())>SUMMARY_LIMIT:raise ValueError('public4MiB summary ceiling')
        try:_publish('FinalNativeGate-setup-terminal.json',summary)
        finally:signal.alarm(0)
    return 78 if failed or errors else 0


if __name__=='__main__':
    raise SystemExit(main())
