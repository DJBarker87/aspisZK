"""Fixed prospective producer source. Public entry is UNCONDITIONALLY DISABLED.

Only a separately reviewed future source patch may connect these private bodies
and fill missing pin artifacts. No caller admission, argv, manifest or callback.
"""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import resource
import signal
import stat
import subprocess
import time
import zoneinfo

HERE = Path(__file__).resolve().parent
STAGE = Path('/home/dombarker/final-native-gate-v6-20261025')
PACKET = STAGE/'FinalNativeGate-packet'
UNIT = 'FinalNativeGate-060'
PROOF = '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/resume-scalar/proof/Cargo.toml'
COMMAND = ('/usr/bin/timeout','240','/home/dombarker/.cargo/bin/cargo','kani',
           '--manifest-path',PROOF,'--lib','--exact','--harness',
           'checks::paired_coordinate_native_resume','--solver','kissat',
           '--output-format','terse','-j','1','-Z','unstable-options','-Z','stubbing',
           '--extra-pointer-checks','--cbmc-args','--unwinding-assertions')
# Seal is generated only from this job's immutable local text inputs.
from FinalNativeGate_seal import PLAN_SHA256

class Denied(RuntimeError):
    pass


def main():
    # No conditional, environment read, flag parser or imported host module.
    print('FinalNativeGate source-only: disabled; lead review/allocation required')
    return 78


def _modules():
    # Called only by private prospective bodies; importing the public CLI is inert.
    import FinalNativeGate_observe as observation
    from FinalNativeGate_guard import Guard, inherited_limits, check_limits, Proc
    return observation, Guard, inherited_limits, check_limits, Proc


def _save(name, value):
    o, *_ = _modules()
    o.save(name, value)


def _plan():
    seal=(HERE/'FinalNativeGate_seal.py').read_text()
    if seal != 'PLAN_SHA256 = '+repr(PLAN_SHA256)+'\n':
        raise Denied('bootstrap seal source drift')
    with (HERE/'FinalNativeGate-plan.json').open('rb') as stream:
        before=os.fstat(stream.fileno())
        if before.st_size>4*2**20:raise Denied('plan stat bound')
        raw=stream.read(4*2**20+1)
        if len(raw)>4*2**20 or before!=os.fstat(stream.fileno()):raise Denied('plan size/identity drift')
    if hashlib.sha256(raw).hexdigest()!=PLAN_SHA256:
        raise Denied('fixed plan source seal drift')
    p=json.loads(raw)
    # No metadata acceptance can supply missing values or enable the public CLI.
    if p['host_runtime'] is None or p['native_runtime_dependencies'] is None or p['cache_inventory'] is None or p['environment'] is None or p['inherited_limits'] is None:
        raise Denied('missing reviewed host runtime/tool/cache/env/rlimit pins; metadata epoch7 is historical only')
    return p


def _tree(roots, catalog):
    from FinalNativeGate_bounded import Reader
    return Reader(catalog).inventory(roots)


def _file_pins(p):
    from FinalNativeGate_bounded import Reader
    catalog=p['catalogs']['source']
    snapshot=Reader(catalog).inventory(catalog['roots'])
    if set(snapshot)!=set(p['files']):raise Denied('source inventory coverage drift')
    files={path:snapshot[path]['sha256'] for path in p['files']}
    if files!=p['files']:raise Denied('fixed source/package/tool drift')
    return files


def _pins():
    p=_plan()
    o,_,limits,check,_=_modules()
    if HERE!=STAGE:raise Denied('wrong fixed staging directory')
    if dict(os.environ)!=p['environment']:raise Denied('environment drift')
    check(limits(),p['inherited_limits'])
    if o.runtime_pins(p['catalogs']['runtime'])!=p['host_runtime']:raise Denied('collector runtime/tool/source drift')
    files=_file_pins(p)
    native=_tree(p['native_roots'],p['catalogs']['native'])
    if native!=p['native_runtime_dependencies']:raise Denied('native tool/sysroot dependency drift')
    cache=_tree(p['cache_roots'],p['catalogs']['cache'])
    if cache!=p['cache_inventory']:raise Denied('cache preflight drift')
    return dict(files=files,native=native,cache=cache,environment=p['environment'],
                inherited_limits=limits(),source_revision=p['source_revision'],
                caveat='observations and file identity, not executed-body or compiler-correctness proof')


def _controls(report=None):
    o,*_=_modules()
    c=o.controls()
    # Retain the actual failing pressure/swap/control snapshot before checking.
    _save('FinalNativeGate-control-'+str(time.monotonic_ns())+'.json',c)
    o.check_controls(c)
    identity={k:v for k,v in c['self_observation'].items() if k!='reads'}
    if Path(identity['path']).name!=UNIT+'.scope':raise Denied('wrong actual scope unit')
    if report is not None:
        if identity!=report['decision']['scope_binding']['self_identity']:
            raise Denied('actual collector/control start identity drift')
    return c


def _admit(phase):
    # Full concrete collector calls its own policy.evaluate, including raw reads,
    # visibility commands and BOTH scan_bound snapshots. No supplied GO verdict.
    o,*_=_modules()
    report=o.collect(phase)
    _save('FinalNativeGate-'+phase+'-decision-'+str(time.monotonic_ns())+'.json',report)
    if report['decision']['allowed'] is not True or report['decision'].get('error') or report['decision'].get('collection_failures'):
        raise Denied('full actual admission denied: '+phase)
    return report


def _charge():
    # An exclusive fixed receipt is the durable one-shot local ledger. Creation
    # failure denies; existence on any later invocation prevents a second launch.
    _save('FinalNativeGate-Kani060-CHARGED.json',dict(schema='FinalNativeGate-charge-v1',
          previous=59,charged=60,command=list(COMMAND),monotonic_ns=time.monotonic_ns(),
          rule='durable before Popen; all frontend/parse/resource/solver/spawn uncertainties charged; no rerun'))


def _cancel_child(proc, fd, expected):
    # pidfd opened before identity recheck, never kill(numeric_pid).
    _,_,_,_,Proc=_modules()
    actual=Proc().optional(proc.pid)
    if actual is None:return 'already absent'
    if actual['starttime']!=expected['starttime'] or actual['ppid']!=os.getpid():
        raise Denied('direct child identity changed; not signalled')
    signal.pidfd_send_signal(fd,signal.SIGKILL)
    return 'owned pidfd SIGKILL'


def _packet_check():
    st=PACKET.lstat()
    if not stat.S_ISDIR(st.st_mode) or st.st_uid!=os.getuid() or st.st_mode & 0o077:
        raise Denied('packet must be owned private directory, never a symlink')


def _execute():
    """No arguments: one fixed Kani child, all admissions internal and fresh."""
    o,Guard,limits,check,Proc=_modules()
    p=_plan();_packet_check();initial=limits();check(initial,p['inherited_limits'])
    guard=Guard();proc=None;fd=None;identity=None;usage=None;code=None
    failed=True;errors=[];start=time.monotonic();before=None
    signal.signal(signal.SIGUSR1,lambda *_: (_ for _ in ()).throw(Denied('resident guard failed')))
    o.ACTIVE_GUARD=guard
    try:
        guard.start()
        pre=_pins();_save('FinalNativeGate-pre.json',pre)
        before=_controls();_save('FinalNativeGate-controls-pre.json',before)
        inside=_admit('inside-scope');_controls(inside)
        # Second concrete fresh GO collection, no old marker accepted.
        go=_admit('go');go_control=_controls(go)
        _save('FinalNativeGate-go-controls.json',go_control)
        go_pins=_pins();_save('FinalNativeGate-go-pins.json',go_pins)
        if go_pins!=pre:raise Denied('pre/GO pin mismatch')
        guard.check();check(limits(),initial)
        # Capture files must open before charge. Failure consumes no Kani slot.
        with (PACKET/'FinalNativeGate-stdout.raw').open('xb') as out, (PACKET/'FinalNativeGate-stderr.raw').open('xb') as err:
            _charge()
            # This is the ONLY Kani invocation site. No retries, flags or callbacks.
            proc=subprocess.Popen(list(COMMAND),cwd=STAGE,env=p['environment'],stdout=out,stderr=err)
            fd=os.pidfd_open(proc.pid)
            identity=Proc().identity(proc.pid)
            if identity['ppid']!=os.getpid():raise Denied('not actual owned child')
            guard.remember(identity,os.getpid())
            _save('FinalNativeGate-child.json',dict(identity=identity,command=list(COMMAND),pidfd_opened=True))
            while True:
                guard.check();_controls(go)
                pid,status,usage_now=os.wait4(proc.pid,os.WNOHANG)
                if pid:
                    usage=usage_now;code=os.waitstatus_to_exitcode(status);proc.returncode=code
                    break
                if time.monotonic()-start>300:
                    # Independent lifecycle ceiling, not a raised solver timeout.
                    raise Denied('outer lifecycle deadline; fixed inner timeout remains240')
                time.sleep(.05)
            out.flush();os.fsync(out.fileno());err.flush();os.fsync(err.fileno())
        post=_pins_after()
        _save('FinalNativeGate-post.json',post)
        if post['files']!=pre['files'] or post['native']!=pre['native']:
            raise Denied('post source/tool/runtime drift')
        _save('FinalNativeGate-controls-post.json',_controls(go))
        if code!=0:raise Denied('actual command failed: '+str(code))
        check(limits(),initial);guard.check();failed=False
    except BaseException as exc:
        errors.append(type(exc).__name__+': '+str(exc))
    finally:
        # Capture/reap/timeout failures are never relabelled as proof success.
        signal.signal(signal.SIGUSR1,signal.SIG_IGN)
        from FinalNativeGate_cleanup import cleanup
        closure=cleanup(proc,fd,identity,guard,_cancel_child)
        errors.extend(closure['errors']);monitor=closure['monitor']
        if closure['usage'] is not None:usage=closure['usage']
        if proc is not None:code=proc.returncode
        if closure['errors'] or closure['unresolved']:failed=True
        o.ACTIVE_GUARD=None
        try:_save('FinalNativeGate-guard.json',monitor)
        except BaseException as exc:
            failed=True;errors.append('guard receipt: '+repr(exc))
        _save('FinalNativeGate-terminal.json',dict(schema='FinalNativeGate-terminal-v1',
              terminal='COMMAND_EXIT_ZERO_PENDING_PROOF_REVIEW' if not failed else 'FAILED',
              actual_command_exit=code,child_spawned=proc is not None,
              direct_cancel_outcome=closure['direct_cancel_outcome'],scope_assessment=closure['scope_assessment'],
              charged=(PACKET/'FinalNativeGate-Kani060-CHARGED.json').exists(),
              wall_seconds=time.monotonic()-start,errors=errors,
              peak_rss_kib=None if usage is None else usage.ru_maxrss,
              swaps=None if usage is None else usage.ru_nswap,
              missing_metrics='null means unobserved; cgroup peak/events in controls receipts',
              print_axioms='N/A: Kani producer source; no Lean declaration',
              security_targets_established=False))
    return 78 if failed else 0


def _cache_after(p):
    # Mutable Cargo outputs have a separately reviewed finite output envelope;
    # neither previous equality nor a new unbounded forest is required.
    from FinalNativeGate_catalog import discover
    from FinalNativeGate_bounded import Reader
    b=p['cache_output_bounds']
    if not b or not b.get('rationale') or not p['cache_roots']:raise Denied('missing reviewed cache output envelope')
    catalog,missing=discover(p['cache_roots'],b['files'],time.monotonic()+b['seconds'])
    if missing or catalog['bounds']['bytes']>b['bytes']:raise Denied('cache output alias/type/size envelope')
    catalog['bounds']=b
    return dict(catalog=catalog,files=Reader(catalog).inventory(p['cache_roots']))


def _pins_after():
    # Cargo outputs legitimately change; retain exact post cache inventory without
    # falsely requiring an immutable output cache. Source/tools remain immutable.
    p=_plan();o,_,limits,check,_=_modules()
    check(limits(),p['inherited_limits'])
    if dict(os.environ)!=p['environment'] or o.runtime_pins(p['catalogs']['runtime'])!=p['host_runtime']:
        raise Denied('post runtime/environment drift')
    return dict(files=_file_pins(p),
                native=_tree(p['native_roots'],p['catalogs']['native']),cache=_cache_after(p))


def _scope_argv():
    p=_plan()
    return ['/usr/bin/systemd-run','--user','--scope','--unit='+UNIT,
            '-p','MemoryHigh=3G','-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64',
            '/usr/bin/env','-i',*[k+'='+v for k,v in sorted(p['environment'].items())],
            '/usr/bin/python3','-I','-B',str(STAGE/'FinalNativeGate_inside.py')]


def _prospective():
    # Fixed fresh packet, terminal even if denial; never overwrite/retry it.
    if HERE!=STAGE:raise Denied('wrong fixed staging directory')
    PACKET.mkdir(mode=0o700,exist_ok=False)
    o,Guard,limits,check,_=_modules();p=_plan();initial=limits();check(initial,p['inherited_limits'])
    hm=datetime.datetime.now(zoneinfo.ZoneInfo('Europe/London')).strftime('%H%M')
    with open('/tmp/aspis-r0-lean.lock','r') as lock:
        if not (hm>='2230' or hm<'1400'):
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        _save('FinalNativeGate-lock.json',dict(path='/tmp/aspis-r0-lean.lock',
             held=not (hm>='2230' or hm<'1400'),inode=os.fstat(lock.fileno()).st_ino))
        guard=Guard();o.ACTIVE_GUARD=guard
        signal.signal(signal.SIGUSR1,lambda *_: (_ for _ in ()).throw(Denied('prospective guard failed')))
        from FinalNativeGate_scope import FixedScope
        scope=FixedScope('final')
        child=None;fd=None;ident=None;failed=True
        try:
            guard.start();parent_pre=_pins();_save('FinalNativeGate-prospective-pins.json',parent_pre)
            _admit('prospective');guard.check()
            scope.preflight()
            argv=scope.argv(p['environment']);_save('FinalNativeGate-scope-argv.json',argv)
            with (PACKET/'FinalNativeGate-scope.stdout').open('xb') as out,(PACKET/'FinalNativeGate-scope.stderr').open('xb') as err:
                child=subprocess.Popen(argv,env=p['environment'],cwd=STAGE,stdout=out,stderr=err)
                fd=os.pidfd_open(child.pid);ident=_modules()[4]().identity(child.pid)
                guard.remember(ident,os.getpid())
                scope.bind_release(child,ident,guard)
                deadline=time.monotonic()+360
                while True:
                    guard.check()
                    pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                    if pid:
                        child.returncode=os.waitstatus_to_exitcode(status);break
                    if time.monotonic()>deadline:raise Denied('scope lifecycle timeout')
                    time.sleep(.05)
                _save('FinalNativeGate-scope-exit.json',dict(exit=child.returncode,peak_rss_kib=usage.ru_maxrss,swap=usage.ru_nswap))
                failed=child.returncode!=0
                out.flush();os.fsync(out.fileno());err.flush();os.fsync(err.fileno())
            parent_post=_pins_after();_save('FinalNativeGate-parent-post-pins.json',parent_post)
            if parent_post['files']!=parent_pre['files'] or parent_post['native']!=parent_pre['native']:
                raise Denied('parent post source/tool drift')
            guard.check();check(limits(),initial)
        except BaseException as exc:
            failed=True
            _save('FinalNativeGate-parent-error.json',dict(error=repr(exc)))
        finally:
            signal.signal(signal.SIGUSR1,signal.SIG_IGN)
            from FinalNativeGate_cleanup import cleanup
            closure=cleanup(child,fd,ident,guard,_cancel_child,scope,outer=True)
            if closure['errors'] or closure['unresolved']:failed=True
            o.ACTIVE_GUARD=None
            # A record-write error must not skip another terminal write attempt.
            for name,value in [('FinalNativeGate-parent-cleanup.json',dict(
                    errors=closure['errors'],unresolved=closure['unresolved'],
                    direct_cancel_outcome=closure['direct_cancel_outcome'],scope=closure['scope'],
                    scope_cancel_outcome=closure['scope_cancel_outcome'],
                    reaped=child is not None and child.returncode is not None)),
                    ('FinalNativeGate-parent-guard.json',closure['monitor'])]:
                try:_save(name,value)
                except BaseException as exc:
                    failed=True;closure['errors'].append('receipt '+name+': '+repr(exc))
            _save('FinalNativeGate-parent-terminal.json',dict(failed=failed,scope_exit=None if child is None else child.returncode,
                  charged=(PACKET/'FinalNativeGate-Kani060-CHARGED.json').exists(),errors=closure['errors'],
                  unresolved=closure['unresolved'],print_axioms='N/A'))
            o.ACTIVE_GUARD=None
    return 78 if failed else 0


if __name__=='__main__':
    raise SystemExit(main())
