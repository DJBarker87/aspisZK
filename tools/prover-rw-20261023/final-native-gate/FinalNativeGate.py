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
STAGE = Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate')
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
    raw=(HERE/'FinalNativeGate-plan.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=PLAN_SHA256:
        raise Denied('fixed plan source seal drift')
    p=json.loads(raw)
    # No metadata acceptance can supply missing values or enable the public CLI.
    if p['host_runtime'] is None or p['native_runtime_dependencies'] is None or p['cache_inventory'] is None or p['environment'] is None or p['inherited_limits'] is None:
        raise Denied('missing reviewed host runtime/tool/cache/env/rlimit pins; metadata epoch7 is historical only')
    return p


def _tree(roots):
    # Fixed roots come from the sealed plan; never a user manifest or CLI path.
    result={}
    for root in roots:
        p=Path(root)
        if not p.exists():raise Denied('missing fixed input: '+root)
        if p.is_dir():
            for directory,dirs,files in os.walk(p,followlinks=True):
                dirs.sort()
                for name in sorted(files):
                    f=Path(directory)/name
                    if not f.is_file():raise Denied('non-file input: '+str(f))
                    result[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest()
        elif p.is_file():result[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
        else:raise Denied('non-file fixed root')
    return result


def _pins():
    p=_plan()
    o,_,limits,check,_=_modules()
    if HERE!=STAGE:raise Denied('wrong fixed staging directory')
    if dict(os.environ)!=p['environment']:raise Denied('environment drift')
    check(limits(),p['inherited_limits'])
    if o.runtime_pins()!=p['host_runtime']:raise Denied('collector runtime/tool/source drift')
    files={path:hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in p['files']}
    if files!=p['files']:raise Denied('fixed source/package/tool drift')
    native=_tree(p['native_roots'])
    if native!=p['native_runtime_dependencies']:raise Denied('native tool/sysroot dependency drift')
    cache=_tree(p['cache_roots'])
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
        if proc is not None and proc.returncode is None:
            try:
                if fd is not None and identity is not None:
                    errors.append(_cancel_child(proc,fd,identity))
                guard.cancel_owned()
                deadline=time.monotonic()+5
                while time.monotonic()<deadline:
                    pid,status,u=os.wait4(proc.pid,os.WNOHANG)
                    if pid:
                        usage=u;code=os.waitstatus_to_exitcode(status);proc.returncode=code;break
                    time.sleep(.05)
                if proc.returncode is None:errors.append('REAP_UNRESOLVED: no successful closure')
            except BaseException as exc:errors.append('cleanup/reap: '+repr(exc))
        if fd is not None:os.close(fd)
        try:
            monitor=guard.finish(failed=failed)
            guard.check()
        except BaseException as exc:monitor=dict(error=repr(exc));failed=True
        o.ACTIVE_GUARD=None
        _save('FinalNativeGate-guard.json',monitor)
        _save('FinalNativeGate-terminal.json',dict(schema='FinalNativeGate-terminal-v1',
              terminal='COMMAND_EXIT_ZERO_PENDING_PROOF_REVIEW' if not failed else 'FAILED',
              actual_command_exit=code,child_spawned=proc is not None,
              charged=(PACKET/'FinalNativeGate-Kani060-CHARGED.json').exists(),
              wall_seconds=time.monotonic()-start,errors=errors,
              peak_rss_kib=None if usage is None else usage.ru_maxrss,
              swaps=None if usage is None else usage.ru_nswap,
              missing_metrics='null means unobserved; cgroup peak/events in controls receipts',
              print_axioms='N/A: Kani producer source; no Lean declaration',
              security_targets_established=False))
    return 78 if failed else 0


def _pins_after():
    # Cargo outputs legitimately change; retain exact post cache inventory without
    # falsely requiring an immutable output cache. Source/tools remain immutable.
    p=_plan();o,_,limits,check,_=_modules()
    check(limits(),p['inherited_limits'])
    if dict(os.environ)!=p['environment'] or o.runtime_pins()!=p['host_runtime']:
        raise Denied('post runtime/environment drift')
    return dict(files={path:hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in p['files']},
                native=_tree(p['native_roots']),cache=_tree(p['cache_roots']))


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
        child=None;fd=None;ident=None;failed=True
        try:
            guard.start();parent_pre=_pins();_save('FinalNativeGate-prospective-pins.json',parent_pre)
            _admit('prospective');guard.check()
            argv=_scope_argv();_save('FinalNativeGate-scope-argv.json',argv)
            with (PACKET/'FinalNativeGate-scope.stdout').open('xb') as out,(PACKET/'FinalNativeGate-scope.stderr').open('xb') as err:
                child=subprocess.Popen(argv,env=p['environment'],cwd=STAGE,stdout=out,stderr=err)
                fd=os.pidfd_open(child.pid);ident=_modules()[4]().identity(child.pid)
                guard.remember(ident,os.getpid())
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
            if child is not None and child.returncode is None:
                if fd is not None and ident is not None:_cancel_child(child,fd,ident)
                guard.cancel_owned()
                deadline=time.monotonic()+5
                reaped=False
                while time.monotonic()<deadline:
                    pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                    if pid:
                        child.returncode=os.waitstatus_to_exitcode(status);reaped=True;break
                    time.sleep(.05)
                _save('FinalNativeGate-parent-cleanup.json',dict(reaped=reaped,exit=child.returncode))
            if fd is not None:os.close(fd)
            monitor=guard.finish(failed=failed)
            if monitor.get('error'):failed=True
            _save('FinalNativeGate-parent-guard.json',monitor)
            _save('FinalNativeGate-parent-terminal.json',dict(failed=failed,scope_exit=None if child is None else child.returncode,
                  charged=(PACKET/'FinalNativeGate-Kani060-CHARGED.json').exists(),print_axioms='N/A'))
            o.ACTIVE_GUARD=None
    return 78 if failed else 0


if __name__=='__main__':
    raise SystemExit(main())
