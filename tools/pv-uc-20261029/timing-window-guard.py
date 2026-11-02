"""Read-only quiet-window authorization and continuous foreign-cgroup guard.

No timing or scopes are launched by importing this module or by --check.
The lead creates the shared marker; this code never changes it.
"""
from pathlib import Path
import argparse, json, math, os, threading, time
MARKER=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
RUN='pv-uc-timing'
class Hold(RuntimeError):pass

def marker_guard(marker=MARKER, now=None, require_live=False):
    now=time.time() if now is None else now
    try:
        raw=marker.read_text()
    except FileNotFoundError:
        if require_live:raise Hold('timing requires a live pv-uc-timing window')
        return dict(allowed=True,active=False,marker=str(marker),now=now,reason='absent: normal admission')
    except OSError as e:raise Hold('unreadable quiet marker: '+str(e)) from e
    try:
        m=json.loads(raw);until=m['until']
        if isinstance(until,bool) or not isinstance(until,(int,float)) or not math.isfinite(until):raise ValueError('until must be a finite number')
    except (ValueError,KeyError,TypeError) as e:raise Hold('invalid quiet marker: '+str(e)) from e
    active=now<until
    if active and m.get('for')!=RUN:raise Hold('foreign live quiet window: '+raw)
    if require_live and not active:raise Hold('timing window expired')
    return dict(allowed=True,active=active,marker=str(marker),now=now,until=until,window=m,
                owner_exception=active and m.get('for')==RUN)

def foreign_scopes(root=Path('/sys/fs/cgroup/user.slice'), own=None):
    """Inventory every populated finite-memory cgroup across users, fail closed.

    cgroup.events populated is hierarchical and catches populated descendants.
    Exclude only our exact capped scope and its ancestors/descendants.
    Unreadable or racing inventory invalidates rather than assuming quiet.
    """
    if own is None:
        own=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
    rows=[]
    def visit(p):
        try:
            # A disappeared directory is no longer a concurrent resource user.
            # Durable UnitNew events separately retain short-lived build scopes.
            with os.scandir(p) as entries:
                children=[Path(e.path) for e in entries if e.is_dir(follow_symlinks=False)]
            if p!=own and p not in own.parents and own not in p.parents:
                maximum=(p/'memory.max').read_text().strip()
                if maximum!='max':
                    events=dict(line.split() for line in (p/'cgroup.events').read_text().splitlines())
                    if events.get('populated') not in ('0','1'):raise Hold('invalid cgroup population: '+str(p))
                    if events['populated']=='1':rows.append(dict(cgroup=str(p),memory_max=int(maximum),events=events))
            for child in children:visit(child)
        except FileNotFoundError:
            if p.exists():raise
    try:visit(root)
    except (OSError,ValueError) as e:raise Hold('cgroup inventory unavailable/raced: '+str(e)) from e
    return rows

def check(marker=MARKER, require_live=True, inventory=foreign_scopes):
    m=marker_guard(marker,require_live=require_live);foreign=inventory()
    if foreign:raise Hold('other capped scope: '+json.dumps(foreign))
    return dict(marker=m,foreign_capped_scopes=foreign,load=os.getloadavg(),now=time.time())

class ScopeEvents:
    """Durable systemd UnitNew subscription for every scope of this build user.

    Subscribe on the same persistent bus connection as the signal match. A
    short-lived scope still leaves a queued signal, even if it is already gone
    when the cgroup inventory runs. Unknown new scopes invalidate conservatively.
    """
    def __init__(self, own_unit=None):
        self.own_unit=own_unit;self.history=[];self.failure=None
        self.stop_event=threading.Event();self.lock=threading.Lock()
        self.lib=None;self.bus=None;self.slot=None;self.thread=None
    def feed_unit(self, unit, path='synthetic'):
        if not unit.endswith('.scope') or unit==self.own_unit:return
        event=dict(unit=unit,path=path,utc=time.time())
        self.history.append(event)
        if self.failure is None:
            self.failure=dict(now=time.time(),reason='new foreign systemd scope (cap unknown; fail closed): '+unit,event=event)
    def _ok(self, code, operation):
        if code<0:raise Hold(operation+': '+os.strerror(-code))
    def _call(self, interface, method):
        self._ok(self.lib.sd_bus_call_method(self.bus,b'org.freedesktop.systemd1',b'/org/freedesktop/systemd1',interface,method,None,None,b''),method.decode())
    def _drain(self):
        while True:
            r=self.lib.sd_bus_process(self.bus,None);self._ok(r,'sd_bus_process')
            if r==0:return
    def start(self):
        import ctypes as C
        self.C=C
        if self.own_unit is None:
            self.own_unit=Path(Path('/proc/self/cgroup').read_text().split('0::')[1].strip()).name
        try:
            self.lib=C.CDLL('libsystemd.so.0');self.bus=C.c_void_p();self.slot=C.c_void_p()
            self.lib.sd_bus_open_user.argtypes=[C.POINTER(C.c_void_p)];self.lib.sd_bus_open_user.restype=C.c_int
            self.lib.sd_bus_process.argtypes=[C.c_void_p,C.c_void_p];self.lib.sd_bus_process.restype=C.c_int
            self.lib.sd_bus_wait.argtypes=[C.c_void_p,C.c_uint64];self.lib.sd_bus_wait.restype=C.c_int
            self.lib.sd_bus_call_method.argtypes=[C.c_void_p,C.c_char_p,C.c_char_p,C.c_char_p,C.c_char_p,C.c_void_p,C.c_void_p,C.c_char_p];self.lib.sd_bus_call_method.restype=C.c_int
            self.lib.sd_bus_message_read.argtypes=[C.c_void_p,C.c_char_p];self.lib.sd_bus_message_read.restype=C.c_int
            self.lib.sd_bus_add_match.argtypes=[C.c_void_p,C.POINTER(C.c_void_p),C.c_char_p,C.c_void_p,C.c_void_p];self.lib.sd_bus_add_match.restype=C.c_int
            for name in ['sd_bus_unref','sd_bus_slot_unref']:
                getattr(self.lib,name).argtypes=[C.c_void_p];getattr(self.lib,name).restype=C.c_void_p
            self.lib.sd_bus_set_method_call_timeout.argtypes=[C.c_void_p,C.c_uint64];self.lib.sd_bus_set_method_call_timeout.restype=C.c_int
            self._ok(self.lib.sd_bus_open_user(C.byref(self.bus)),'sd_bus_open_user')
            self._ok(self.lib.sd_bus_set_method_call_timeout(self.bus,2_000_000),'bus call timeout')
            callback_type=C.CFUNCTYPE(C.c_int,C.c_void_p,C.c_void_p,C.c_void_p)
            def receive(message, userdata, error):
                try:
                    unit=C.c_char_p();path=C.c_char_p()
                    self._ok(self.lib.sd_bus_message_read(message,b'so',C.byref(unit),C.byref(path)),'UnitNew decode')
                    self.feed_unit(unit.value.decode(),path.value.decode())
                except BaseException as exc:self.failure=dict(now=time.time(),reason='scope event callback: '+str(exc))
                return 0
            self.callback=callback_type(receive)
            match=b"type='signal',sender='org.freedesktop.systemd1',interface='org.freedesktop.systemd1.Manager',member='UnitNew'"
            self._ok(self.lib.sd_bus_add_match(self.bus,C.byref(self.slot),match,C.cast(self.callback,C.c_void_p),None),'UnitNew match')
            self._call(b'org.freedesktop.systemd1.Manager',b'Subscribe')
            self.thread=threading.Thread(target=self._loop,daemon=True);self.thread.start();return self
        except BaseException as exc:
            self.failure=dict(now=time.time(),reason='scope event subscription unavailable: '+str(exc));self.close();raise Hold(self.failure['reason']) from exc
    def _loop(self):
        try:
            while not self.stop_event.is_set() and self.failure is None:
                with self.lock:
                    self._drain()
                    r=self.lib.sd_bus_wait(self.bus,50_000)
                    if r!=-4:self._ok(r,'sd_bus_wait')
                self.stop_event.wait(0.001)
        except BaseException as exc:self.failure=dict(now=time.time(),reason='scope event stream failed: '+str(exc))
    def sync(self):
        # A round trip flushes earlier UnitNew signals before accepting a pair.
        with self.lock:
            self._call(b'org.freedesktop.DBus.Peer',b'Ping');self._drain()
        if self.failure:raise Hold(self.failure['reason'])
    def close(self):
        self.stop_event.set()
        if self.thread:self.thread.join(timeout=3)
        if self.thread and self.thread.is_alive():raise Hold('scope event thread did not stop')
        if self.lib:
            if self.slot and self.slot.value:self.lib.sd_bus_slot_unref(self.slot);self.slot=None
            if self.bus and self.bus.value:self.lib.sd_bus_unref(self.bus);self.bus=None

class Monitor:
    """Sticky failure: a transient foreign job invalidates the current pair.

    Cgroup inventory runs every 50 ms. The timing runner also enables a
    persistent UnitNew subscription, so short-lived scopes from either
    stream of this shared build user cannot vanish between inventories.
    Sample-boundary bus round trips drain queued creation events.
    """
    def __init__(self, probe=check, interval=0.05, event_watch=False):
        self.probe=probe;self.interval=interval;self.stop_event=threading.Event()
        self.failure=None;self.checks=0;self.thread=None;self.events=None;self.event_watch=event_watch
    def poll(self):
        if self.failure is not None:raise Hold(self.failure['reason'])
        if self.events and self.events.failure:
            self.failure=dict(self.events.failure,checks=self.checks);raise Hold(self.failure['reason'])
        try:r=self.probe();self.checks+=1;return r
        except BaseException as e:
            self.failure=dict(now=time.time(),reason=str(e),checks=self.checks)
            raise Hold(str(e)) from e
    def _loop(self):
        while not self.stop_event.wait(self.interval):
            try:self.poll()
            except Hold:return
    def start(self):
        try:
            if self.event_watch:self.events=ScopeEvents();self.events.start()
            self.poll();self.thread=threading.Thread(target=self._loop,daemon=True);self.thread.start();return self
        except BaseException:self.close();raise
    def checkpoint(self):
        try:
            if self.events:self.events.sync()
            return self.poll()
        except BaseException as exc:
            self.failure=dict(now=time.time(),reason=str(exc),checks=self.checks)
            raise Hold(str(exc)) from exc
    def close(self):
        self.stop_event.set()
        if self.thread:self.thread.join()
        if self.events:self.events.close()
    def __enter__(self):return self.start()
    def __exit__(self,*args):self.close()

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true',required=True);p.add_argument('--require-live',action='store_true');p.add_argument('--marker',type=Path,default=MARKER);a=p.parse_args()
    print(json.dumps(marker_guard(a.marker,require_live=a.require_live),indent=2))
