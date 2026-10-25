"""Synthetic-only syscall/order and strict trace tests. No Linux backend invoked."""
import copy, hashlib, json
from SbfClosure_receipt import run
import SbfClosure_setup as s
from SbfClosure_trace import Join, TraceDenied

class ExecReached(Exception):pass

class Fake:
    def __init__(self,fail=None):self.calls=[];self.entered=False;self.fail=fail
    def op(self,name):
        self.calls.append(name)
        if self.fail==name:raise s.Denied('synthetic '+name)
    def namespaces(self):
        self.op('namespaces')
        return {k:(k+'new' if self.entered else k+'old') for k in ('mnt','net','pid')}
    def unshare(self,flags):self.op('unshare');self.entered=True
    def fork_guest(self):self.op('fork_guest')
    def mount(self,*args):self.op('mount')
    def exec(self,*args):self.op('exec');raise ExecReached()
    def __getattr__(self,name):return lambda *args:self.op(name)

def manifest():
    return dict(root=s.ROOT,own=s.OWN,uid=1000,gid=1000,argv=list(s.PROBE),env=s.ENV.copy(),
        scope=dict(swap_max=0,tasks_max=64,memory_high=3*1024**3,memory_max=4*1024**3),
        files=[dict(logical='/usr/bin/python3',physical='/reviewed/python3',type='regular',mode=0o755,bytes=10,sha256='a'*64,public_kind='runtime')],
        devices=['null','zero','urandom'],writable=['/tmp','/home/dombarker/.probe-work'],
        go=dict(parent_pid=123,parent_start_ticks=456,cgroup='0::/own\n',receipt_path='/reviewed/go.json',receipt_sha256='b'*64))

def approved(m):return (hashlib.sha256((json.dumps(m,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest(),)

def main():
    tests=[]
    for failure in ('host_gate','unshare','fork_guest','mount','create_root','copy_sealed','make_links','assert_mount','assert_private_proc','devices','close_fds_and_stdio','chroot_fd','drop_all','assert_child'):
        m=manifest();f=Fake(failure)
        try:s.prepare(m,f,approved(m))
        except s.Denied:pass
        else:raise AssertionError(failure)
        assert 'exec' not in f.calls
        if failure in ('host_gate','unshare','fork_guest'):assert 'mount' not in f.calls
        tests.append('failure '+failure+' prevents child exec')
    for key,value in [('root','/'),('own','/tmp/foreign'),('uid',0),('gid',0),('argv',['/bin/sh']),('env',{'SECRET':'leak'}),('devices',['null']),('writable',['/home'])]:
        m=manifest();m[key]=value;f=Fake()
        try:s.prepare(m,f,approved(m))
        except s.Denied:pass
        else:raise AssertionError(key)
        assert not f.calls;tests.append('manifest rejects '+key)
    m=manifest();f=Fake()
    try:s.prepare(m,f)
    except s.Denied:pass
    else:raise AssertionError('empty approval gate')
    assert not f.calls;tests.append('unapproved manifest fails before host checks')
    class WrongNamespace(Fake):
        def namespaces(self):return {k:'same' for k in ('mnt','net','pid')}
    f=WrongNamespace()
    try:s.prepare(m,f,approved(m))
    except s.Denied:pass
    else:raise AssertionError('wrong namespace')
    assert 'mount' not in f.calls;tests.append('wrong namespace prevents any mount')
    f=Fake()
    try:s.prepare(m,f,approved(m))
    except ExecReached:pass
    assert f.calls.index('unshare')<f.calls.index('mount')<f.calls.index('chroot_fd')<f.calls.index('drop_all')<f.calls.index('exec')
    tests.append('synthetic order reaches exact probe only')
    def row(kind='regular',link=None):
        ident=dict(bytes=1,sha256='c'*64,mode=0o644)
        if link:ident={'link':link,'mode':0o777}
        return dict(physical='/private/input',type=kind,pre=ident,go=ident.copy(),post=ident.copy())
    seals={'/src':row('directory'),'/src/input':row(),'/tool':row(),'/out/build-script':row()}
    def trace(lines):
        j=Join(10,'/src',copy.deepcopy(seals),{'/out/new'})
        for line in lines:j.line(line)
        return j.finish()
    good=['10 1.000 openat(AT_FDCWD, "input", O_RDONLY|O_CLOEXEC) = 3',
          '10 1.001 clone(child_stack=NULL, flags=SIGCHLD) = 11',
          '11 1.002 execve("/out/build-script", ["/out/build-script"], 0xabc /* 2 vars */) = 0',
          '11 1.003 openat(AT_FDCWD, "/out/new", O_WRONLY|O_CREAT, 0600) = 3',
          '11 1.004 close(3) = 0','11 1.005 exit_group(0) = ?',
          '10 1.006 close(3) = 0','10 1.007 exit_group(0) = ?']
    result=trace(good);assert result['execs'][0]['pid']==11 and result['fresh_outputs']==['/out/new']
    tests.append('fork/direct Cargo build-script exec/CLOEXEC/fresh output join')
    bad=['10 1.0 openat(8, "input", O_RDONLY) = 3',
         '10 1.0 openat(AT_FDCWD, "/unknown", O_RDONLY) = -1 ENOENT (No such file)',
         '10 1.0 clone(child_stack=NULL, flags=CLONE_FILES|SIGCHLD) = 11',
         '10 1.0 execve("/tool", ["/tool", ...], 0xabc /* 2 vars */) = 0',
         '10 1.0 readlink("/unknown", "x", 4) = 1',
         '10 1.0 openat(AT_FDCWD, "/src/input", O_WRONLY) = 3',
         '12 1.0 exit_group(0) = ?',
         '10 1.0 close(9) = 0',
         '10 1.0 wait4(11, NULL, 0, NULL) = 11',
         '10 1.0 openat(AT_FDCWD, "input", O_RDONLY <unfinished ...>',
         'strace: Process 11 detached']
    for line in bad:
        try:trace([line])
        except TraceDenied:pass
        else:raise AssertionError(line)
        tests.append('trace denial '+line)
    try:trace(good[:-1])
    except TraceDenied:tests.append('lost live descendant denied')
    else:raise AssertionError('incomplete trace')
    changed=copy.deepcopy(seals);changed['/tool']['post']['sha256']='d'*64
    try:Join(10,'/src',changed,set())
    except TraceDenied:tests.append('pre/GO/post drift denied')
    else:raise AssertionError('drift')
    return dict(tests=tests,count=len(tests),namespace_executed=False,privileged_backend_executed=False,
        limitations='Orchestrator fake failures do NOT test real mount/capability/ownership syscall semantics. Linux backend and actual strace compatibility unprobed.')

if __name__=='__main__':raise SystemExit(run('synthetic-tests.receipt.json',main))
