"""Fixed owned user scopes. Private future bodies; tests replace OS boundaries.

systemd/procfs are trusted operational observations, not a kernel semantics proof.
No unit-name kill: cancellation targets only a retained verified cgroup fd.
"""
import json
import os
from pathlib import Path
import selectors
import signal
import stat
import subprocess
import time
from FinalNativeGate_guard import Proc

STAGE=Path('/home/dombarker/final-native-gate-v12-20261025')
PROFILES={
    'final':('FinalNativeGate-060',3*2**30,4*2**30,'FinalNativeGate-packet','FinalNativeGate_inside.py'),
    'setup':('FinalNativeGate-pin-setup',768*2**20,2**30,'FinalNativeGate-setup-packet','FinalNativeGate_setup_inside.py')}
PROPERTIES=('LoadState','ActiveState','SubState','InvocationID','ActiveEnterTimestampMonotonic','ControlGroup')


def bounded(path,limit=65536,dir_fd=None):
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=dir_fd)
    try:
        chunks=[];size=0
        while True:
            piece=os.read(fd,min(65536,limit+1-size))
            if not piece:break
            chunks.append(piece);size+=len(piece)
            if size>limit:raise ValueError('bounded metadata overflow')
        raw=b''.join(chunks)
        return raw.decode('utf-8','strict')
    finally:os.close(fd)


def command(argv,timeout=5,limit=65536,*,record=False):
    """Fixed metadata command only; five-second/output ceiling, stable cancellation."""
    p=subprocess.Popen(argv,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                       env=environment(),close_fds=True)
    fd=None;chunks={};deadline=time.monotonic()+min(timeout,15)
    try:
        fd=os.pidfd_open(p.pid)
        with selectors.DefaultSelector() as sel:
            for stream in (p.stdout,p.stderr):sel.register(stream,selectors.EVENT_READ);chunks[stream]=bytearray()
            while sel.get_map():
                if time.monotonic()>deadline:raise TimeoutError('fixed systemctl metadata deadline')
                for key,_ in sel.select(.05):
                    data=os.read(key.fileobj.fileno(),4096)
                    if not data:sel.unregister(key.fileobj);continue
                    chunks[key.fileobj].extend(data)
                    if sum(map(len,chunks.values()))>limit:raise ValueError('fixed metadata output bound')
        p.wait(timeout=max(.001,deadline-time.monotonic()))
        if p.returncode:raise ValueError('systemctl metadata nonzero: '+str(p.returncode))
        stdout=bytes(chunks[p.stdout]).decode('utf-8','strict');stderr=bytes(chunks[p.stderr]).decode('utf-8','strict')
        return subprocess.CompletedProcess(argv,p.returncode,stdout,stderr) if record else stdout
    except BaseException as exc:
        exc.stdout=bytes(chunks.get(p.stdout,b'')).decode('utf-8','replace')
        exc.stderr=bytes(chunks.get(p.stderr,b'')).decode('utf-8','replace')
        raise
    finally:
        try:
            if p.poll() is None and fd is not None:signal.pidfd_send_signal(fd,signal.SIGKILL)
            if p.poll() is None:p.wait(timeout=1)
        finally:
            if fd is not None:os.close(fd)
            p.stdout.close();p.stderr.close()


def environment():
    # Fixed proposal, UID observed as candidate operating metadata, no inherited env.
    uid=os.getuid()
    return dict(HOME='/home/dombarker',USER='dombarker',LOGNAME='dombarker',
                PATH='/usr/bin:/bin',LANG='C.UTF-8',LC_ALL='C.UTF-8',
                XDG_RUNTIME_DIR='/run/user/'+str(uid),
                DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/'+str(uid)+'/bus')


def membership(pid):
    lines=bounded('/proc/'+str(pid)+'/cgroup').splitlines()
    if len(lines)!=1 or not lines[0].startswith('0::/'):raise ValueError('not unified cgroup membership')
    return lines[0][3:]


def durable(packet,name,value):
    s=packet.lstat()
    if not stat.S_ISDIR(s.st_mode) or s.st_uid!=os.getuid() or s.st_mode&0o077:raise ValueError('private owned packet required')
    raw=json.dumps(value,sort_keys=True).encode()
    if len(raw)>65536:raise ValueError('handshake bound')
    # Link only after fsync: no partial ready/release visible to another reader.
    tmp=packet/(name+'.partial')
    with tmp.open('xb') as f:f.write(raw);f.flush();os.fsync(f.fileno())
    os.link(tmp,packet/name,follow_symlinks=False)
    fd=os.open(packet,os.O_DIRECTORY|os.O_RDONLY|os.O_NOFOLLOW)
    try:os.fsync(fd)
    finally:os.close(fd)


def child_wait(kind):
    """Called by each concrete private inside entry BEFORE any workload/collector."""
    unit,_,_,name,_=PROFILES[kind];packet=STAGE/name
    row=Proc().identity(os.getpid());cg=membership(row['pid'])
    if not cg.endswith('/'+unit+'.scope'):raise ValueError('inside fixed unit mismatch')
    ready=dict(pid=row['pid'],starttime=row['starttime'],ppid=row['ppid'],cgroup=cg)
    durable(packet,'scope-ready.json',ready)
    deadline=time.monotonic()+20
    while time.monotonic()<deadline:
        try:release=json.loads(bounded(packet/'scope-release.json'))
        except FileNotFoundError:time.sleep(.02);continue
        current=Proc().identity(os.getpid())
        if release.get('ready')!=ready or current['starttime']!=ready['starttime'] or membership(row['pid'])!=cg:
            raise ValueError('release identity drift')
        if not release.get('invocation'):raise ValueError('missing parent invocation binding')
        return release
    raise TimeoutError('parent binding handshake20s; workload never admitted')


class FixedScope:
    def __init__(self,kind):
        self.kind=kind
        self.unit,self.high,self.cap,name,self.inside=PROFILES[kind]
        self.packet=STAGE/name;self.fd=None;self.binding=None;self.events=[];self.prebind_failure=None

    def show(self,timeout=5):
        argv=['/usr/bin/systemctl','--user','show',self.unit+'.scope','--no-pager',
              '--property='+','.join(PROPERTIES)]
        raw=command(argv,timeout=timeout);rows={}
        self.events.append(dict(command=argv,raw=raw))
        # A bounded tail also preserves malformed prebinding observations.
        del self.events[:-8]
        for line in raw.splitlines():
            k,v=line.split('=',1)
            if k in rows:raise ValueError('duplicate systemctl property')
            rows[k]=v
        if set(rows)!=set(PROPERTIES):raise ValueError('incomplete systemctl identity')
        return rows

    def preflight(self):
        if self.show()['LoadState']!='not-found':raise ValueError('fixed unit already exists; no adoption')

    def argv(self,env):
        return ['/usr/bin/systemd-run','--user','--scope','--unit='+self.unit,
                '-p','MemoryHigh='+str(self.high),'-p','MemoryMax='+str(self.cap),
                '-p','MemorySwapMax=0','-p','TasksMax=64',
                '/usr/bin/env','-i',*[k+'='+v for k,v in sorted(env.items())],
                '/usr/bin/python3','-I','-B',str(STAGE/self.inside)]

    def note_read_failure(self,name,exc):
        # Diagnostics only. No removal/ownership decision is changed.
        row=dict(kind='retained-scope-read-failure',operation=name,errno=exc.errno,
                 error=repr(exc)[:1024],fd=self.fd,kernel=os.uname().release,
                 bound_group=None if self.binding is None else self.binding['group'])
        if self.fd is not None:
            try:
                s=os.fstat(self.fd)
                row['fstat']=dict(dev=s.st_dev,ino=s.st_ino,nlink=s.st_nlink,
                                  uid=s.st_uid,gid=s.st_gid,mode=s.st_mode)
            except OSError as failure:row['fstat_error']=repr(failure)[:1024]
            try:row['proc_fd_link']=os.readlink('/proc/self/fd/'+str(self.fd))[:4096]
            except OSError as failure:row['proc_fd_link_error']=repr(failure)[:1024]
            try:row['fdinfo']=bounded('/proc/self/fdinfo/'+str(self.fd),limit=4096)
            except (OSError,ValueError) as failure:row['fdinfo_error']=repr(failure)[:1024]
        self.events.append(row);del self.events[:-8]

    def read(self,name):
        try:return bounded(name,dir_fd=self.fd)
        except OSError as exc:
            self.note_read_failure(name,exc)
            raise

    def open_group(self,cg):
        if not cg.startswith('/') or '..' in cg.split('/') or not cg.endswith('/'+self.unit+'.scope'):
            raise ValueError('invalid fixed cgroup path')
        fd=os.open('/sys/fs/cgroup',os.O_DIRECTORY|os.O_RDONLY|os.O_NOFOLLOW)
        try:
            for part in cg.split('/')[1:]:
                if not part:raise ValueError('empty cgroup component')
                nxt=os.open(part,os.O_DIRECTORY|os.O_RDONLY|os.O_NOFOLLOW,dir_fd=fd)
                os.close(fd);fd=nxt
            self.fd=fd;fd=None
        finally:
            if fd is not None:os.close(fd)

    def controls(self):
        expected={'memory.high':self.high,'memory.max':self.cap,'memory.swap.max':0,'pids.max':64}
        for name,value in expected.items():
            if self.read(name).strip()!=str(value):raise ValueError('fixed control drift: '+name)
        if self.read('memory.swap.current').strip()!='0':raise ValueError('scope swap observed')

    def group_identity(self):
        try:s=os.fstat(self.fd)
        except OSError as exc:
            self.note_read_failure('group_identity',exc)
            raise
        if not stat.S_ISDIR(s.st_mode) or s.st_uid!=os.getuid() or s.st_mode&0o022:raise ValueError('scope owner/permissions')
        return [s.st_dev,s.st_ino,s.st_uid,s.st_gid,s.st_mode]

    def current(self):
        row=self.show()
        if row!=self.binding['unit']:raise ValueError('unit invocation/start/path/state changed; no name-based cancellation')
        if self.group_identity()!=self.binding['group']:raise ValueError('retained scope identity drift')
        # Reopen path: descriptor retention alone does not detect name replacement.
        held=self.fd
        try:
            self.open_group(row['ControlGroup'])
            if self.group_identity()!=self.binding['group']:raise ValueError('scope inode replaced')
        finally:
            if self.fd!=held:os.close(self.fd)
            self.fd=held
        self.controls()
        return row

    def bind_release(self,child,wrapper,guard):
        deadline=time.monotonic()+20
        while time.monotonic()<deadline:
            guard.check()
            if child.poll() is not None:raise ValueError('wrapper exited before binding')
            try:ready=json.loads(bounded(self.packet/'scope-ready.json'))
            except FileNotFoundError:time.sleep(.02);continue
            try:row=self.show(timeout=max(.001,min(5,deadline-time.monotonic())))
            except BaseException as exc:
                self.prebind_failure=dict(reason=repr(exc),stdout=getattr(exc,'stdout','')[:65536],stderr=getattr(exc,'stderr','')[:65536])
                raise
            failed=[]
            if row['LoadState']!='loaded':failed.append('LoadState')
            if row['ActiveState']!='active':failed.append('ActiveState')
            if not row['InvocationID']:failed.append('InvocationID')
            stamp=row['ActiveEnterTimestampMonotonic']
            if not stamp.isdigit() or int(stamp)<=0:failed.append('ActiveEnterTimestampMonotonic')
            if failed:
                self.prebind_failure=dict(reason='scope has no live invocation/start',failed_fields=failed,row=dict(row))
                time.sleep(min(.02,max(0,deadline-time.monotonic())))
                continue
            # Only readiness is retried. Every ownership/control failure is fatal.
            guard.check()
            if child.poll() is not None:raise ValueError('wrapper exited before binding')
            if time.monotonic()>=deadline:break
            self.open_group(row['ControlGroup']);group=self.group_identity();self.controls()
            proc=Proc();actual=proc.identity(ready['pid'])
            if any(actual[k]!=ready[k] for k in ('pid','starttime','ppid')):raise ValueError('ready proc start mismatch')
            if membership(actual['pid'])!=row['ControlGroup'] or ready['cgroup']!=row['ControlGroup']:
                raise ValueError('ready membership mismatch')
            # Wrapper may itself be the exec child; otherwise bounded lineage.
            ancestor=actual
            for _ in range(16):
                if ancestor['pid']==wrapper['pid']:break
                ancestor=proc.identity(ancestor['ppid'])
            else:raise ValueError('ready child not owned wrapper descendant')
            if ancestor['starttime']!=wrapper['starttime']:raise ValueError('wrapper reused')
            if membership(os.getpid())==row['ControlGroup']:raise ValueError('outer parent inside workload scope')
            if str(actual['pid']) not in self.read('cgroup.procs').split():raise ValueError('child absent from retained cgroup')
            self.binding=dict(unit=row,group=group,ready=ready)
            self.current()
            again=proc.identity(ready['pid'])
            if again['starttime']!=ready['starttime'] or membership(ready['pid'])!=row['ControlGroup'] or child.poll() is not None:
                raise ValueError('child exited/moved before release')
            guard.check()
            if time.monotonic()>=deadline:raise TimeoutError('fixed scope binding deadline20s before release')
            durable(self.packet,'scope-binding.json',self.binding)
            guard.check()
            if child.poll() is not None:raise ValueError('wrapper exited before release')
            if time.monotonic()>=deadline:raise TimeoutError('fixed scope binding deadline20s before release')
            durable(self.packet,'scope-release.json',dict(ready=ready,invocation=row['InvocationID']))
            return self.binding
        raise TimeoutError('fixed scope binding deadline20s')

    def removed(self):
        # Kernel removal of a retained cgroup requires no live tasks/descendants.
        # Treat replacement or unreadable unit metadata as unresolved, not absence.
        if os.fstat(self.fd).st_nlink!=0:return False
        row=self.show();old=self.binding['unit']
        same_inactive=(row['InvocationID']==old['InvocationID'] and
            row['ActiveEnterTimestampMonotonic']==old['ActiveEnterTimestampMonotonic'] and
            row['ActiveState']=='inactive' and row['ControlGroup'] in ('',old['ControlGroup']))
        if row['LoadState']!='not-found' and not same_inactive:return False
        try:os.stat('/sys/fs/cgroup'+old['ControlGroup'],follow_symlinks=False)
        except FileNotFoundError:
            self.events.append(dict(terminal='verified removed retained inode and unit absent/same invocation inactive'))
            return True
        return False

    def empty(self):
        if self.fd is None or self.binding is None:raise ValueError('scope ownership unbound')
        if self.group_identity()!=self.binding['group']:raise ValueError('scope descriptor identity drift')
        # Double empty read on retained identity, or verified kernel removal.
        try:
            for _ in range(2):
                events=dict(line.split() for line in self.read('cgroup.events').splitlines())
                if events.get('populated')!='0' or self.read('cgroup.procs').split() or self.read('cgroup.threads').split():return False
        except OSError as exc:
            if exc.errno not in (2,19) or not self.removed():raise
        return True

    def cancel_owned(self):
        if self.empty():return 'verified-bound-scope-empty'
        self.current()  # refuse replacement invocation/path/inode/control drift
        fd=os.open('cgroup.kill',os.O_WRONLY|os.O_NOFOLLOW,dir_fd=self.fd)
        try:os.write(fd,b'1\n')
        finally:os.close(fd)
        return 'verified-bound-cgroup-kill-requested'

    def finish(self):
        deadline=time.monotonic()+5
        while time.monotonic()<deadline:
            if self.empty():
                terminal=self.show()  # unreadable terminal identity is unresolved
                return dict(unresolved=False,binding=self.binding,events=self.events,terminal_unit=terminal,
                            identity_status='same invocation' if terminal['InvocationID']==self.binding['unit']['InvocationID'] else 'old retained scope empty; terminal unit absent/replaced, never killed by name')
            time.sleep(.05)
        return dict(unresolved=True,binding=self.binding,events=self.events,reason='scope still populated/tasks; retain packet and fd control path')

    def close(self):
        if self.fd is not None:os.close(self.fd);self.fd=None
