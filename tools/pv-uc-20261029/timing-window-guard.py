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
        # scandir propagates errors unlike a suppressing pathlib glob.
        with os.scandir(p) as entries:
            children=[Path(e.path) for e in entries if e.is_dir(follow_symlinks=False)]
        if p!=own and p not in own.parents and own not in p.parents:
            maximum=(p/'memory.max').read_text().strip()
            events=dict(line.split() for line in (p/'cgroup.events').read_text().splitlines())
            if events.get('populated') not in ('0','1'):raise Hold('invalid cgroup population: '+str(p))
            if maximum!='max' and events['populated']=='1':
                rows.append(dict(cgroup=str(p),memory_max=int(maximum),events=events))
        for child in children:visit(child)
    try:visit(root)
    except (OSError,ValueError) as e:raise Hold('cgroup inventory unavailable/raced: '+str(e)) from e
    return rows

def check(marker=MARKER, require_live=True, inventory=foreign_scopes):
    m=marker_guard(marker,require_live=require_live);foreign=inventory()
    if foreign:raise Hold('other capped scope: '+json.dumps(foreign))
    return dict(marker=m,foreign_capped_scopes=foreign,load=os.getloadavg(),now=time.time())

class Monitor:
    """Sticky failure: a transient foreign job invalidates the current pair.

    Poll every 50 ms throughout both client calls and between them, with
    synchronous checks at each sample boundary. This is sampled detection;
    scopes shorter than the sampling interval are not claimed impossible.
    """
    def __init__(self, probe=check, interval=0.05):
        self.probe=probe;self.interval=interval;self.stop_event=threading.Event()
        self.failure=None;self.checks=0;self.thread=None
    def poll(self):
        if self.failure is not None:raise Hold(self.failure['reason'])
        try:r=self.probe();self.checks+=1;return r
        except BaseException as e:
            self.failure=dict(now=time.time(),reason=str(e),checks=self.checks)
            raise Hold(str(e)) from e
    def _loop(self):
        while not self.stop_event.wait(self.interval):
            try:self.poll()
            except Hold:return
    def start(self):
        self.poll();self.thread=threading.Thread(target=self._loop,daemon=True);self.thread.start();return self
    def close(self):
        self.stop_event.set()
        if self.thread:self.thread.join()
    def __enter__(self):return self.start()
    def __exit__(self,*args):self.close()

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true',required=True);p.add_argument('--require-live',action='store_true');p.add_argument('--marker',type=Path,default=MARKER);a=p.parse_args()
    print(json.dumps(marker_guard(a.marker,require_live=a.require_live),indent=2))
