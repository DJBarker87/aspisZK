"""Independent cleanup attempts; errors are retained, never success evidence."""
import os
import time


def cleanup(child,fd,identity,guard,cancel):
    errors=[]; usage=None; monitor=None
    def attempt(label,action):
        try:return action()
        except BaseException as exc:
            errors.append(label+': '+repr(exc));return None
    if child is not None and child.returncode is None:
        if fd is not None and identity is not None:
            attempt('direct cancellation',lambda:cancel(child,fd,identity))
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
    # A pidfd/lineage shutdown cannot certify no future or reparented children.
    # Until the outer bound-cgroup shutdown interface is reviewed, deny closure.
    unresolved=child is not None
    if unresolved:errors.append('SCOPE_UNRESOLVED: bound outer cgroup shutdown not implemented; retain packet/control path')
    return dict(errors=errors,usage=usage,monitor=monitor,unresolved=unresolved)
