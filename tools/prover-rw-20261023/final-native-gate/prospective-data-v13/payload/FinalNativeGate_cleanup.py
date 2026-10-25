"""Independent cleanup attempts; errors are retained, never success evidence."""
import os
import time


def cleanup(child,fd,identity,guard,cancel,scope=None,*,outer=False,spawn_state=None):
    errors=[]; usage=None; monitor=None; direct=None; scope_cancel=None; scope_result=None
    def attempt(label,action):
        try:return action()
        except BaseException as exc:
            errors.append(label+': '+repr(exc));return None
    no_owned_start=(spawn_state=='not_started' and child is None and fd is None and identity is None
                    and scope is not None and scope.fd is None and scope.binding is None)
    if no_owned_start:
        scope_result=dict(status='not_started',owned_handle=False,unresolved=False,
                          reason='same execution never attempted Popen; no child, pidfd, scope fd or binding')
    if scope is not None and not no_owned_start:
        scope_cancel=attempt('scope-wide cancellation',scope.cancel_owned)
    if child is not None and child.returncode is None:
        if fd is not None and identity is not None:
            direct=attempt('direct cancellation',lambda:cancel(child,fd,identity))
        else:errors.append('direct cancellation: missing stable handle/identity')
    # Always attempt descendants, including after direct child has exited.
    attempt('descendant cancellation',guard.cancel_owned)
    if child is not None and child.returncode is None:
        deadline=time.monotonic()+5
        while time.monotonic()<deadline:
            value=attempt('reap',lambda:os.wait4(child.pid,os.WNOHANG))
            if value is None:break
            pid,status,u=value
            if pid:
                child.returncode=os.waitstatus_to_exitcode(status);usage=u;break
            time.sleep(.05)
        if child.returncode is None:errors.append('REAP_UNRESOLVED')
    if fd is not None:attempt('pidfd close',lambda:os.close(fd))
    monitor=attempt('guard finish',lambda:guard.finish(failed=bool(errors)))
    attempt('guard final check',guard.check)
    if monitor and monitor.get('error'):errors.append('guard: '+str(monitor['error']))
    if monitor:
        for row in monitor.get('cancellations',[]):
            if row['outcome'] not in ('disappeared','verified-owned-signalled'):
                errors.append('descendant unresolved: '+repr(row))
    if scope is not None and not no_owned_start:
        scope_result=attempt('scope terminal verification',scope.finish)
    if scope is not None and not no_owned_start and scope_result is None:
        scope_result=dict(unresolved=True,binding=scope.binding,events=list(scope.events),
                          prebind_failure=getattr(scope,'prebind_failure',None),
                          reason='scope terminal verification failed; ownership/closure unresolved')
    unresolved=bool((child is not None or spawn_state=='uncertain') and outer and
                    (scope_result is None or scope_result.get('unresolved',True)))
    if unresolved:errors.append('SCOPE_UNRESOLVED: retain packet/control path; no finite kernel termination promise')
    if scope is not None and not unresolved and not no_owned_start:attempt('scope descriptor close',scope.close)
    return dict(errors=errors,usage=usage,monitor=monitor,unresolved=unresolved,
                direct_cancel_outcome=direct,scope_cancel_outcome=scope_cancel,scope=scope_result,
                scope_assessment='not_started; no owned scope control attempted' if no_owned_start else 'outer verified' if outer else 'deferred to outer bound scope')
