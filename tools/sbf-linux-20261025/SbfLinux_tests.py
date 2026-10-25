"""Pure/mock tests only: no CDLL, syscall, fork, exec, limits or credentials."""
import ctypes as C
import errno
import importlib
import json
import pathlib
import types
import unittest
from unittest.mock import Mock, patch
import SbfLinux_abi as A
import SbfLinux_backend as B
from SbfLinux_capture import Denied, ROOT

class ChildExit(BaseException):
    pass

class MockC:
    def __init__(self):
        self.calls=[]; self.signatures={}; self.fail=None; self.nextfd=30
        self.capzero=True;self.options=[];self.clonefields=None
    def bind(self,name,types_):
        self.signatures[name]=types_
        def run(number,*args):
            self.calls.append((name,number.value,args))
            if self.fail == name:
                C.set_errno(errno.EPERM);return -1
            if name=='fsconfig' and args[1].value==1:
                self.options.append((args[2],C.string_at(args[3])))
            if name=='statx':
                p=C.cast(args[-1],C.POINTER(A.Statx)).contents
                p.mask=0x1000;p.mnt_id=123
            if name=='getrlimit':
                p=C.cast(args[-1],C.POINTER(A.Rlimit)).contents
                p.cur=p.max=2**40
            if name=='clone3':
                p=C.cast(args[0],C.POINTER(A.CloneArgs)).contents
                self.clonefields=tuple(getattr(p,n) for n in ('flags','exit_signal','stack','stack_size','tls','cgroup'))
                C.cast(p.pidfd,C.POINTER(A.I)).contents.value=40
                return 1234
            if name=='prctl':
                return 1 if args[0].value==39 else 0
            if name in ('open_tree','fsopen','fsmount','pidfd_open'):
                self.nextfd+=1;return self.nextfd
            return 0
        return run
    def abi(self):
        return A.LinuxABI(self.bind,'Linux','x86_64')

class AbiTests(unittest.TestCase):
    def setUp(self):
        self.c=MockC();self.a=self.c.abi()
    def test_layout(self):
        A.layout_check()
        self.assertEqual((C.sizeof(A.Statx),A.Statx.mnt_id.offset),(256,144))
        self.assertEqual(C.sizeof(A.CloneArgs),88)
    def test_wrong_platform_before_binder_or_cdll(self):
        for platform,machine in [('Darwin','x86_64'),('Linux','aarch64')]:
            binder=Mock(side_effect=AssertionError('binder effect'))
            with patch.object(A.C,'CDLL',side_effect=AssertionError('CDLL effect')):
                with self.assertRaises(Denied):A.LinuxABI(binder,platform,machine)
            binder.assert_not_called()
    def test_unreviewed_kernel_before_loading(self):
        with patch.object(A.platform,'release',return_value='6.9.0'),patch.object(A.C,'CDLL',side_effect=AssertionError('load')):
            with self.assertRaises(Denied):A.LinuxABI(None,'Linux','x86_64')
    def test_signatures_and_numbers_from_source(self):
        root=pathlib.Path(__file__).resolve().parents[2]/'evidence/sbf-linux-20261025'
        tbl=(root/'SbfLinux-ref-arch_x86_entry_syscalls_syscall_64.tbl').read_text()
        entries={f[2]:int(f[0]) for l in tbl.splitlines()
                 if (f:=l.split()) and f[0].isdigit() and f[1] in ('common','64')}
        for name,(number,types_) in A.SPECS.items():
            self.assertEqual(entries[name],number)
            self.assertEqual(self.c.signatures[name],types_)
        self.assertEqual(A.SPECS['mount_setattr'][1],
                         (A.I,A.S,A.U,C.POINTER(A.MountAttr),C.c_size_t))
        self.assertEqual(A.SPECS['fsconfig'][1],(A.I,A.U,A.S,A.P,A.I))
    def test_descriptor_tree_flags(self):
        self.a.tree(19)
        n,num,args=self.c.calls[-1]
        self.assertEqual((n,num),('open_tree',428))
        self.assertEqual((args[0].value,args[1],args[2].value),
                         (19,b'',0x1000|0x80000|1|0x100|0x800))
    def test_descriptor_attach_flags(self):
        self.a.attach(31,19)
        _,_,args=self.c.calls[-1]
        self.assertEqual([args[0].value,args[1],args[2].value,args[3],args[4].value],
                         [31,b'',19,b'',0x44])
    def test_attr_bytes_and_size(self):
        captured=[]
        def binder(name,types_):
            fn=self.c.bind(name,types_)
            def f(n,*args):
                if name=='mount_setattr':
                    x=C.cast(args[3],C.POINTER(A.MountAttr)).contents
                    captured.append((args[0].value,args[1],args[2].value,
                        x.attr_set,x.attr_clr,x.propagation,x.userns_fd,args[4].value))
                return fn(n,*args)
            return f
        a=A.LinuxABI(binder,'Linux','x86_64')
        a.attr(8,7,A.PRIVATE,True)
        self.assertEqual(captured,[(8,b'',0x9000,7,0,1<<18,0,32)])
    def test_filesystems_fixed_finite(self):
        closed=[];self.a.filesystem('tmpfs',closed.append)
        self.assertEqual(len(closed),1)
        names=[n for n,_,_ in self.c.calls]
        self.assertEqual(names,['fsopen']+['fsconfig']*6+['fsmount'])
        rows=[args for n,_,args in self.c.calls if n=='fsconfig']
        self.assertEqual([r[2] for r in rows],[b'size',b'nr_inodes',b'mode',b'uid',b'gid',None])
        self.assertEqual(self.c.calls[-1][2][-1].value,14)
        self.assertEqual(self.c.options,[(b'size',b'1048576'),(b'nr_inodes',b'64'),(b'mode',b'1777'),(b'uid',b'0'),(b'gid',b'0')])
        with self.assertRaises(Denied):self.a.filesystem('ext4',closed.append)
    def test_proc_readonly_flags(self):
        self.a.filesystem('proc',lambda fd:None)
        self.assertEqual(self.c.calls[-1][2][-1].value,15)
    def test_errno_for_every_syscall(self):
        for name,(_,types_) in A.SPECS.items():
            with self.subTest(name=name):
                self.c.fail=name
                with self.assertRaises(OSError) as ctx:
                    self.a.call(name,*[t() for t in types_])
                self.assertEqual(ctx.exception.errno,errno.EPERM)
    def test_fsconfig_failure_closes_context(self):
        self.c.fail='fsconfig';closed=[]
        with self.assertRaises(OSError):self.a.filesystem('tmpfs',closed.append)
        self.assertEqual(closed,[31])
        self.assertNotIn('fsmount',[n for n,_,_ in self.c.calls])
    def test_statx_actual_mask(self):
        self.assertEqual(self.a.mount_id(3),123)
        a=A.LinuxABI(lambda n,t:lambda *args:0,'Linux','x86_64')
        with self.assertRaises(Denied):a.mount_id(3)
    def test_clone_atomic_pidfd_and_layout(self):
        self.assertEqual(self.a.fork_pidfd(),(1234,40))
        self.assertEqual(self.c.calls[-1][2][1].value,88)
        self.assertEqual(self.c.clonefields,(0x1000,17,0,0,0,0))
    def test_clone_python_hook_order_and_failure(self):
        events=[]
        self.a.fork_hooks=tuple((lambda n=n:events.append(n)) for n in ('before','parent','child'))
        self.a.fork_pidfd()
        self.assertEqual(events,['before','parent'])
        events.clear();self.c.fail='clone3'
        with self.assertRaises(OSError):self.a.fork_pidfd()
        self.assertEqual(events,['before','parent'])
    def test_clone_child_hook(self):
        a=A.LinuxABI(lambda n,t:lambda *args:0,'Linux','x86_64')
        events=[];a.fork_hooks=tuple((lambda n=n:events.append(n)) for n in ('before','parent','child'))
        self.assertEqual(a.fork_pidfd(),(0,-1))
        self.assertEqual(events,['before','child'])
    def test_complete_drop_order_and_ambient_queries(self):
        self.a.drop(40)
        names=[n for n,_,_ in self.c.calls]
        self.assertEqual(names[0],'setgroups')
        self.assertLess(names.index('setresgid'),names.index('setresuid'))
        self.assertLess(names.index('setresuid'),names.index('capset'))
        drops=[a for n,_,a in self.c.calls if n=='prctl' and a[0].value==24]
        self.assertEqual([a[1].value for a in drops],list(range(41)))
        amb=[a for n,_,a in self.c.calls if n=='prctl' and a[0].value==47 and a[1].value==1]
        self.assertEqual([a[2].value for a in amb],list(range(41)))
        with self.assertRaises(Denied):self.a.drop(41)
    def test_drop_failure_stops(self):
        for name in ('setgroups','prctl','setresgid','setresuid','capset','capget'):
            self.c=MockC();self.a=self.c.abi();self.c.fail=name
            with self.subTest(name=name),self.assertRaises(OSError):self.a.drop(40)
            self.assertNotIn('execve',[n for n,_,_ in self.c.calls])
    def test_close_range_and_guest_only_limits(self):
        self.a.close_escape_fds();self.a.guest_limits()
        names=[n for n,_,_ in self.c.calls]
        self.assertEqual(names,['close_range','getrlimit','setrlimit','getrlimit','setrlimit'])
        args=self.c.calls[0][2]
        self.assertEqual([x.value for x in args],[3,0xffffffff,0])
        self.assertEqual([r[2][0].value for r in self.c.calls if r[0]=='setrlimit'],[7,1])
    def test_owned_signal_not_numeric_pid(self):
        self.a.kill_owned(47)
        name,num,args=self.c.calls[-1]
        self.assertEqual((name,num),('pidfd_send_signal',424))
        self.assertEqual((args[0].value,args[1].value,args[2],args[3].value),(47,9,None,0))

class MountMock:
    def __init__(self,fail=None):
        self.events=[];self.fail=fail;self.ids={10:1,20:2,30:3,31:4,40:2,41:2,42:2}
        self.fsindex=0
    def event(self,name,*args):
        self.events.append((name,*args))
        if self.fail==name:raise Denied(name)
    def attr(self,*a,**k):self.event('attr',*a,k)
    def mount_id(self,fd):self.event('id',fd);return self.ids[fd]
    def tree(self,fd):self.event('tree',fd);return 20
    def attach(self,m,t):self.event('attach',m,t)
    def filesystem(self,kind,close):
        self.event('filesystem',kind);self.fsindex+=1;return 29+self.fsindex

class MountTests(unittest.TestCase):
    def setUp(self):
        self.a=MountMock();self.api=Mock();self.api.open.return_value=5
        self.api.fstat.return_value=types.SimpleNamespace(st_uid=0,st_mode=0o41777)
        self.targets=iter((40,41,42))
        self.table={2:dict(path=ROOT,parent=1,options={'ro','nosuid','nodev'},fs='ext4'),
                    3:dict(path=ROOT+'/tmp',parent=2,options={'rw','nosuid','nodev','noexec'},fs='tmpfs'),
                    4:dict(path=ROOT+'/proc',parent=2,options={'ro','nosuid','nodev','noexec'},fs='proc')}
        self.calls=0
    def tablefn(self,*args):
        self.calls+=1
        return {} if self.calls<=2 else self.table
    def runmount(self):
        with patch.object(B,'mount_table',side_effect=self.tablefn),patch.object(
                B,'subdirectory',side_effect=lambda root,name,api: self.target(root,name)):
            return B.mount_guest(10,self.a,self.api)
    def target(self,root,name):
        self.assertEqual(root,20)
        return next(self.targets)
    def test_retained_new_mount_used_for_all_targets(self):
        self.assertEqual(self.runmount(),(20,{'root':2,'tmp':3,'proc':4}))
        attach=[r for r in self.a.events if r[0]=='attach']
        self.assertEqual(attach,[('attach',20,10),('attach',30,40),('attach',31,41)])
        self.assertEqual(self.a.events[0][0],'attr')
        self.assertEqual(self.a.events[0][-1],{'propagation':A.PRIVATE,'recursive':True})
        self.assertIn(('attr',20,7,{}),self.a.events)
    def test_underlying_fd_clone_rejected(self):
        self.a.ids[20]=1
        with self.assertRaises(Denied):self.runmount()
        self.assertFalse(any(e[0]=='attach' for e in self.a.events))
    def test_target_wrong_mount_rejected(self):
        self.a.ids[40]=1
        with self.assertRaises(Denied):self.runmount()
        self.assertNotIn(('filesystem','tmpfs'),self.a.events)
    def test_mount_failures_close_new_root(self):
        for failure in ('attr','tree','attach','filesystem'):
            self.setUp();self.a.fail=failure
            with self.subTest(failure=failure),self.assertRaises(Denied):self.runmount()
            if failure in ('attach','filesystem'):self.api.close.assert_any_call(20)
    def test_wrong_flags_or_topology_rejected(self):
        for field in ('options','parent','fs'):
            self.setUp()
            self.table[3][field]={'rw'} if field=='options' else 99 if field=='parent' else 'ext4'
            with self.subTest(field=field),self.assertRaises(Denied):self.runmount()
    def test_source_submount_rejected(self):
        self.tablefn=lambda *args:self.table
        with self.assertRaises(Denied):self.runmount()
        self.assertFalse(any(e[0]=='tree' for e in self.a.events))

class MetadataTests(unittest.TestCase):
    def test_fd_inventory_closed_inspection_vs_live_high_fd(self):
        api=Mock();api.listdir.return_value=['0','1','2','3','999999']
        api.fstat.side_effect=lambda fd: (_ for _ in ()).throw(OSError(errno.EBADF,'closed')) if fd==3 else object()
        self.assertEqual(B.inventory(api),[0,1,2,999999])
    def test_fd_inventory_non_ebadf_denied(self):
        api=Mock();api.listdir.return_value=['3'];api.fstat.side_effect=OSError(errno.EPERM,'bad')
        with self.assertRaises(Denied):B.inventory(api)
    def test_bounded_read_closes(self):
        api=Mock();api.open.return_value=9;api.read.side_effect=[b'xxxxx']
        with self.assertRaises(Denied):B.read_small('fixed',api,4)
        api.close.assert_called_once_with(9)
    def test_namespace_change_and_no_userns(self):
        before=dict(mnt=1,net=2,pid=3,user=4);current=dict(mnt=11,net=12,pid=13,user=4)
        api=Mock();api.getpid.return_value=1
        with patch.object(B,'namespaces',return_value=current),patch.object(B,'status',return_value={'Threads':'1'}):
            self.assertEqual(B.child_namespaces(before,api),current)
            current['user']=5
            with self.assertRaises(Denied):B.child_namespaces(before,api)
    def test_private_proc_uses_actual_ns_inodes(self):
        api=Mock();api.getpid.return_value=1;api.O_RDONLY=0;api.O_CLOEXEC=0x80000
        api.fstat.return_value=types.SimpleNamespace(st_dev=1,st_ino=3)
        ns={'pid':(1,3)}
        with patch.object(B,'namespaces',return_value=ns):B.private_proc_check(ns,api)
        api.fstat.return_value=types.SimpleNamespace(st_dev=1,st_ino=4)
        with self.assertRaises(Denied):B.private_proc_check(ns,api)
    def test_mount_propagation_denied(self):
        raw=b'2 1 0:1 / / rw shared:2 - ext4 none rw\n'
        with patch.object(B,'read_small',return_value=raw),self.assertRaises(Denied):B.mount_table(Mock())
    def test_mount_private_parse(self):
        raw=b'2 1 0:1 / / ro,nosuid,nodev - ext4 none ro\n'
        with patch.object(B,'read_small',return_value=raw):
            self.assertEqual(B.mount_table(Mock())[2]['options'],{'ro','nosuid','nodev'})

class GuestTests(unittest.TestCase):
    def setUp(self):
        self.events=[];self.api=Mock()
        self.api.fstat.return_value=types.SimpleNamespace(st_dev=1,st_ino=4)
        self.api._exit.side_effect=ChildExit()
        self.api.execve.side_effect=lambda *args:self.events.append('exec')
        self.abi=Mock();self.abi.mount_id.return_value=2
        for name in ('close_escape_fds','guest_limits','drop'):
            getattr(self.abi,name).side_effect=lambda *a,n=name:self.events.append(n)
        self.stages={'child_namespaces':{},'mount_guest':(20,{'root':2}),
                     'stdio_install':{},'private_proc_check':None,'stdio_check':None,
                     'dropped_check':None}
    def run_guest(self,fail=None):
        from contextlib import ExitStack
        with ExitStack() as stack:
            for name,result in self.stages.items():
                def fn(*args,n=name,r=result):
                    self.events.append(n)
                    if n==fail:raise Denied(n)
                    return r
                stack.enter_context(patch.object(B,name,side_effect=fn))
            B.guest(10,Mock(),12,{},b'0::/test\n',40,self.abi,self.api)
    def test_fixed_exec_after_all_checks(self):
        with self.assertRaises(ChildExit):self.run_guest()
        self.assertLess(self.events.index('close_escape_fds'),self.events.index('guest_limits'))
        self.assertLess(self.events.index('drop'),self.events.index('dropped_check'))
        self.assertLess(self.events.index('dropped_check'),self.events.index('exec'))
        self.api.fchdir.assert_called_once_with(20)
        self.api.chroot.assert_called_once_with('.')
        self.api.execve.assert_called_once_with(B.FIXED_PROBE[0],B.FIXED_PROBE,dict(B.ENV))
    def test_every_stage_failure_prevents_exec(self):
        for stage in self.stages:
            self.setUp()
            with self.subTest(stage=stage),self.assertRaises(ChildExit):self.run_guest(stage)
            self.api.execve.assert_not_called()
    def test_native_failure_prevents_exec(self):
        for name in ('close_escape_fds','guest_limits','drop'):
            self.setUp();getattr(self.abi,name).side_effect=Denied(name)
            with self.subTest(name=name),self.assertRaises(ChildExit):self.run_guest()
            self.api.execve.assert_not_called()
    def test_chroot_failure_no_host_fallback(self):
        self.api.chroot.side_effect=OSError(errno.EPERM,'chroot')
        with self.assertRaises(ChildExit):self.run_guest()
        self.api.execve.assert_not_called()

class LifecycleTests(unittest.TestCase):
    def setUp(self):
        self.api=Mock();self.api.WNOHANG=1;self.api.pipe2.return_value=(50,51);self.api.write.return_value=1
        self.abi=Mock();self.clock=Mock()
        self.clock.monotonic.side_effect=[0,0.1,6]
    def test_wait_success(self):
        self.api.waitpid.return_value=(123,0)
        self.assertEqual(B.owned_wait(123,44,self.abi,self.api,self.clock),(123,0))
        self.abi.kill_owned.assert_not_called()
    def test_timeout_kills_pidfd_and_reaps(self):
        self.api.waitpid.side_effect=[(0,0),(123,9)]
        with self.assertRaises(Denied):B.owned_wait(123,44,self.abi,self.api,self.clock)
        self.abi.kill_owned.assert_called_once_with(44)
        self.assertEqual(self.api.waitpid.call_args_list[-1].args,(123,0))
    def test_wrong_wait_never_promoted(self):
        self.api.waitpid.return_value=(999,0)
        with self.assertRaises(Denied):B.owned_wait(123,44,self.abi,self.api,self.clock)
    def test_unshare_failure_before_fork_mount(self):
        self.abi.zero.side_effect=OSError(errno.EPERM,'unshare')
        with patch.object(B,'root_helper_preflight',return_value=({},b'x',40)):
            with self.assertRaises(OSError):B.internal_backend(10,Mock(),12,self.abi,self.api,self.clock)
        self.abi.fork_pidfd.assert_not_called()
    def test_gate_child_failure_always_exits_even_cleanup_failure(self):
        self.abi.fork_pidfd.return_value=(0,-1)
        self.api.read.return_value=b''
        self.abi.close_escape_fds.side_effect=Denied('close failure')
        self.api._exit.side_effect=ChildExit()
        with patch.object(B,'root_helper_preflight',return_value=({},b'x',40)),patch.object(B,'guest') as g:
            with self.assertRaises(ChildExit):B.internal_backend(10,Mock(),12,self.abi,self.api,self.clock)
        g.assert_not_called();self.api._exit.assert_called_once_with(126)
    def test_signal_permission_failure_keeps_child_gated(self):
        self.abi.fork_pidfd.return_value=(123,44);self.abi.call.return_value=45
        self.abi.check_owned_signal.side_effect=OSError(errno.EPERM,'signal')
        self.api.waitpid.return_value=(123,9)
        with patch.object(B,'root_helper_preflight',return_value=({},b'x',40)),patch.object(B,'pidfd_identity'):
            with self.assertRaises(OSError):B.internal_backend(10,Mock(),12,self.abi,self.api,self.clock)
        self.api.write.assert_not_called();self.abi.kill_owned.assert_called_once_with(44)
    def test_parent_actual_hostpid_and_collection(self):
        self.abi.fork_pidfd.return_value=(123,44);self.abi.call.return_value=45
        output=Mock()
        with patch.object(B,'root_helper_preflight',return_value=({},b'x',40)),patch.object(
                B,'pidfd_identity') as identity,patch.object(B,'owned_wait',return_value=(123,0)):
            B.internal_backend(10,output,12,self.abi,self.api,self.clock)
        self.assertEqual(identity.call_args_list[0].args,(44,123,self.api))
        output.collect.assert_called_once_with(123,123,0)
        self.api.close.assert_any_call(44);self.api.close.assert_any_call(45)
    def test_parent_validation_failure_kills_own_child(self):
        self.abi.fork_pidfd.return_value=(123,44);self.api.waitpid.return_value=(123,9)
        with patch.object(B,'root_helper_preflight',return_value=({},b'x',40)),patch.object(
                B,'pidfd_identity',side_effect=Denied('identity')):
            with self.assertRaises(Denied):B.internal_backend(10,Mock(),12,self.abi,self.api,self.clock)
        self.abi.kill_owned.assert_called_once_with(44)
        self.api.waitpid.assert_called_once_with(123,0)
    def test_pidfd_metadata_actual_match(self):
        with patch.object(B,'read_small',return_value=b'Pid:\t123\nNSpid:\t123\n'):
            B.pidfd_identity(44,123,self.api)
            with self.assertRaises(Denied):B.pidfd_identity(44,999,self.api)

class DropAndStdioTests(unittest.TestCase):
    def setUp(self):
        self.api=Mock()
        self.api.getresuid.return_value=self.api.getresgid.return_value=(1000,1000,1000)
        self.api.getgroups.return_value=[]
        self.api.stat.return_value=types.SimpleNamespace(st_dev=1,st_ino=2)
        self.s={k:'0' for k in ('CapInh','CapPrm','CapEff','CapBnd','CapAmb')}
        self.s.update(NoNewPrivs='1',Threads='1')
        self.abi=Mock();self.abi.prctl.return_value=1
    def check(self):
        with patch.object(B,'status',return_value=self.s),patch.object(B,'read_small',return_value=b'0::/scope\n'),patch.object(B,'private_proc_check'),patch.object(B,'stdio_check'):
            B.dropped_check({},b'0::/scope\n',(1,2),{},self.abi,self.api)
    def test_all_drop_properties(self):
        self.check()
        for key in ('CapInh','CapPrm','CapEff','CapBnd','CapAmb'):
            self.s[key]='1'
            with self.subTest(key=key),self.assertRaises(Denied):self.check()
            self.s[key]='0'
    def test_saved_id_or_groups_rejected(self):
        self.api.getresuid.return_value=(1000,1000,0)
        with self.assertRaises(Denied):self.check()
        self.api.getresuid.return_value=(1000,)*3;self.api.getgroups.return_value=[0]
        with self.assertRaises(Denied):self.check()
    def test_nnp_and_cgroup_and_root_drift(self):
        self.s['NoNewPrivs']='0'
        with self.assertRaises(Denied):self.check()
        self.s['NoNewPrivs']='1';self.api.stat.return_value=types.SimpleNamespace(st_dev=1,st_ino=999)
        with self.assertRaises(Denied):self.check()
        with patch.object(B,'status',return_value=self.s),patch.object(B,'read_small',return_value=b'0::/other\n'):
            with self.assertRaises(Denied):B.dropped_check({},b'0::/scope\n',(1,2),{},self.abi,self.api)
    def test_stdio_highfd_rejected(self):
        with patch.object(B,'inventory',return_value=[0,1,2,999999]),self.assertRaises(Denied):
            B.stdio_check({},self.api)
    def test_stdio_inodes_and_root_output_modes(self):
        null=types.SimpleNamespace(st_dev=1,st_ino=1,st_mode=0o20666,st_rdev=259)
        out=types.SimpleNamespace(st_dev=1,st_ino=2,st_mode=0o100600,st_uid=0,st_nlink=1)
        self.api.fstat.side_effect=lambda fd:null if fd==0 else out
        self.api.major.return_value=1;self.api.minor.return_value=3
        with patch.object(B,'inventory',return_value=[0,1,2]):
            B.stdio_check({0:(1,1),1:(1,2),2:(1,2)},self.api)
            out.st_mode=0o100666
            with self.assertRaises(Denied):B.stdio_check({0:(1,1),1:(1,2),2:(1,2)},self.api)
    def test_parent_gate_failure_never_collects(self):
        api=Mock();api.pipe2.return_value=(50,51);api.write.return_value=1
        api.waitpid.return_value=(123,9)
        abi=Mock();abi.fork_pidfd.return_value=(123,44);abi.call.side_effect=OSError(errno.ENOSYS,'pidfd_open')
        output=Mock()
        with patch.object(B,'root_helper_preflight',return_value=({},b'x',40)),patch.object(B,'pidfd_identity'):
            with self.assertRaises(OSError):B.internal_backend(10,output,12,abi,api)
        api.write.assert_not_called();output.collect.assert_not_called()
        abi.kill_owned.assert_called_once_with(44)

class DisabledTests(unittest.TestCase):
    def test_all_entrypoints_unconditionally_deny(self):
        for fn in (B.privileged_entrypoint,B.fresh_host_admission):
            with patch.object(A.C,'CDLL',side_effect=AssertionError('native load')):
                with self.assertRaises(Denied):fn()
        self.assertIsNone(B.RUNTIME_APPROVAL);self.assertIsNone(B.PRODUCER_ASSEMBLY)
    def test_postexec_is_fixed_source(self):
        self.assertEqual(B.FIXED_PROBE[:-1],B.PROBE[:-1])
        for text in ('os.getpid()==1',"'/proc/1/ns/pid'",'CapBnd','CapAmb',
                     'getresuid','getresgid','1048576','f_files<=64'):
            self.assertIn(text,B.FIXED_PROBE[-1])
        import ast
        ast.parse(B.FIXED_PROBE[-1])

if __name__=='__main__':
    unittest.main(verbosity=2)
