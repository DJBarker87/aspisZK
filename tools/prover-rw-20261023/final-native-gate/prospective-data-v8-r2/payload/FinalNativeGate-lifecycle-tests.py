"""Explicit mocks/synthetic data only. Never run lifecycle or native commands."""
import ast
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace as NS
import unittest
from unittest.mock import Mock,MagicMock,patch
import FinalNativeGate_scope as s
import FinalNativeGate_candidate as d
import FinalNativeGate_cleanup as c

HERE=Path(__file__).resolve().parent
ROW=dict(LoadState='loaded',ActiveState='active',SubState='running',InvocationID='a'*32,
         ActiveEnterTimestampMonotonic='100',ControlGroup='/user.slice/FinalNativeGate-060.scope')
READY=dict(pid=12,ppid=11,starttime=120,cgroup=ROW['ControlGroup'])
WRAPPER=dict(pid=11,ppid=1,starttime=110)


def bound():
    scope=s.FixedScope('final');scope.fd=99
    scope.binding=dict(unit=dict(ROW),group=[1,2,3,4,5],ready=dict(READY))
    scope.group_identity=Mock(return_value=[1,2,3,4,5]);scope.show=Mock(return_value=dict(ROW))
    scope.controls=Mock();scope.open_group=Mock()
    return scope


class Lifecycle(unittest.TestCase):
    def test_systemctl_metadata_is_fixed_and_bounded_interface(self):
        scope=s.FixedScope('setup')
        raw=''.join(k+'='+v+'\n' for k,v in dict(ROW,ControlGroup='/user.slice/FinalNativeGate-pin-setup.scope').items())
        with patch.object(s,'command',return_value=raw) as command:
            scope.show()
        self.assertEqual(command.call_args.args[0],['/usr/bin/systemctl','--user','show','FinalNativeGate-pin-setup.scope','--no-pager','--property='+','.join(s.PROPERTIES)])

    def test_metadata_command_output_bound_cancels_pidfd_and_reaps(self):
        p=Mock();p.pid=123;p.poll.return_value=None;p.returncode=None
        sel=MagicMock();sel.__enter__.return_value=sel;sel.get_map.return_value=True
        sel.select.return_value=[(NS(fileobj=p.stdout),1)]
        with patch.object(s,'environment',return_value={'SYNTHETIC':'true'}),patch.object(s.subprocess,'Popen',return_value=p),patch.object(s.selectors,'DefaultSelector',return_value=sel),patch.object(s.os,'pidfd_open',return_value=99,create=True),patch.object(s.os,'read',return_value=b'overflow'),patch.object(s.os,'close'),patch.object(s.signal,'pidfd_send_signal',create=True) as cancel,self.assertRaisesRegex(ValueError,'output bound'):
            s.command(['/usr/bin/systemctl','--user','show'],limit=1)
        cancel.assert_called_once_with(99,s.signal.SIGKILL);p.wait.assert_called_once()

    def test_fixed_profiles_and_argv(self):
        for kind,unit,high,cap in [('final','FinalNativeGate-060',3*2**30,4*2**30),('setup','FinalNativeGate-pin-setup',768*2**20,2**30)]:
            scope=s.FixedScope(kind);argv=scope.argv({'HOME':'/home/dombarker'})
            self.assertEqual(argv[:4],['/usr/bin/systemd-run','--user','--scope','--unit='+unit])
            for v in ['MemoryHigh='+str(high),'MemoryMax='+str(cap),'MemorySwapMax=0','TasksMax=64']:self.assertIn(v,argv)
        with self.assertRaises(KeyError):s.FixedScope('caller-unit')

    def test_preexisting_unit_never_adopted(self):
        scope=bound()
        with self.assertRaises(ValueError):scope.preflight()

    def bind(self,scope,*,early=False,drift=False,member=True,release_error=False):
        child=NS(poll=Mock(return_value=0 if early else None));guard=NS(check=Mock())
        scope.show=Mock(return_value=dict(ROW));scope.open_group=Mock();scope.controls=Mock();scope.current=Mock()
        scope.read=Mock(return_value='12\n' if member else '')
        proc=Mock()
        def identity(pid):
            if pid==12:return dict(READY,starttime=121 if drift else 120)
            if pid==11:return WRAPPER
            raise AssertionError('unexpected pid')
        proc.identity.side_effect=identity
        with patch.object(s,'bounded',return_value=json.dumps(READY)),patch.object(s,'Proc',return_value=proc),patch.object(s,'membership',side_effect=lambda pid: '/' if pid==1 else ROW['ControlGroup']),patch.object(s.os,'getpid',return_value=1),patch.object(s,'durable',side_effect=OSError('write') if release_error else None) as write:
            result=scope.bind_release(child,WRAPPER,guard)
        return result,write

    def test_binding_precedes_exclusive_release(self):
        scope=bound();result,write=self.bind(scope)
        self.assertEqual(result['ready'],READY)
        self.assertEqual([call.args[1] for call in write.call_args_list],['scope-binding.json','scope-release.json'])
        scope.current.assert_called_once()

    def test_fast_exit_never_releases(self):
        with self.assertRaisesRegex(ValueError,'before binding'):self.bind(bound(),early=True)

    def test_start_drift_never_releases(self):
        with self.assertRaisesRegex(ValueError,'start mismatch'):self.bind(bound(),drift=True)

    def test_membership_never_releases(self):
        with self.assertRaisesRegex(ValueError,'absent'):self.bind(bound(),member=False)

    def test_release_write_fault_propagates(self):
        with self.assertRaises(OSError):self.bind(bound(),release_error=True)

    def test_unreadable_ready_not_success(self):
        scope=bound()
        with patch.object(s,'bounded',side_effect=PermissionError('ready')),self.assertRaises(PermissionError):scope.bind_release(NS(poll=lambda:None),WRAPPER,NS(check=lambda:None))

    def test_handshake_deadline_no_go(self):
        scope=bound()
        with patch.object(s.time,'monotonic',side_effect=[0,21]),self.assertRaises(TimeoutError):scope.bind_release(NS(),WRAPPER,NS())

    def test_child_release_cannot_supply_arbitrary_go(self):
        with patch.object(s,'Proc') as proc,patch.object(s.os,'getpid',return_value=12),patch.object(s,'membership',return_value=READY['cgroup']),patch.object(s,'durable'),patch.object(s,'bounded',return_value=json.dumps({'ready':dict(READY,starttime=121),'invocation':'a'})):
            proc.return_value.identity.return_value=READY
            with self.assertRaisesRegex(ValueError,'release identity drift'):s.child_wait('final')

    def test_clean_empty_can_resolve(self):
        scope=bound();scope.read=Mock(side_effect=lambda name:'populated 0\nfrozen 0\n' if name=='cgroup.events' else '')
        self.assertTrue(scope.empty());self.assertFalse(scope.finish()['unresolved'])
        self.assertEqual(scope.cancel_owned(),'verified-bound-scope-empty')

    def test_wrapper_exit_does_not_close_orphan_scope(self):
        scope=bound();scope.read=Mock(return_value='populated 1\n')
        self.assertFalse(scope.empty())
        with patch.object(s.time,'monotonic',side_effect=[0,6]):self.assertTrue(scope.finish()['unresolved'])

    def test_replacement_invocation_not_killed(self):
        scope=bound();scope.empty=Mock(return_value=False);scope.show.return_value=dict(ROW,InvocationID='b'*32)
        with patch.object(s.os,'open') as opened,self.assertRaisesRegex(ValueError,'invocation'):scope.cancel_owned()
        opened.assert_not_called()

    def test_replacement_inode_not_killed(self):
        scope=bound();scope.empty=Mock(return_value=False);scope.group_identity.side_effect=[[1,2,3,4,5],[1,6,3,4,5]]
        with patch.object(s.os,'open') as opened,self.assertRaisesRegex(ValueError,'inode'):scope.cancel_owned()
        opened.assert_not_called()

    def test_control_drift_not_killed(self):
        scope=bound();scope.empty=Mock(return_value=False);scope.controls.side_effect=ValueError('control drift')
        with patch.object(s.os,'open') as opened,self.assertRaisesRegex(ValueError,'control drift'):scope.cancel_owned()
        opened.assert_not_called()

    def test_cgroup_cancel_uses_retained_fd(self):
        scope=bound();scope.empty=Mock(return_value=False)
        with patch.object(s.os,'open',return_value=50) as opened,patch.object(s.os,'write') as write,patch.object(s.os,'close'):
            self.assertEqual(scope.cancel_owned(),'verified-bound-cgroup-kill-requested')
        self.assertEqual(opened.call_args.kwargs['dir_fd'],99);write.assert_called_once_with(50,b'1\n')

    def test_permissions_fail_closed(self):
        scope=s.FixedScope('setup');scope.fd=99
        with patch.object(s.os,'fstat',return_value=NS(st_mode=0o40777,st_uid=123)),patch.object(s.os,'getuid',return_value=123),self.assertRaisesRegex(ValueError,'permissions'):scope.group_identity()

    def test_cleanup_independent_faults_and_actual_cancel_telemetry(self):
        guard=NS(cancel_owned=Mock(side_effect=OSError('descendants')),finish=Mock(side_effect=OSError('finish')),check=Mock(side_effect=OSError('check')))
        scope=NS(cancel_owned=Mock(side_effect=OSError('scope')),finish=Mock(return_value={'unresolved':False}),close=Mock())
        child=NS(pid=12,returncode=None);cancel=Mock(return_value='actual direct result')
        with patch.object(c.os,'wait4',side_effect=OSError('reap')),patch.object(c.os,'close',side_effect=OSError('close')):
            result=c.cleanup(child,99,READY,guard,cancel,scope,outer=True)
        self.assertEqual(result['direct_cancel_outcome'],'actual direct result')
        for fn in [guard.cancel_owned,guard.finish,guard.check,scope.finish,scope.close]:fn.assert_called_once()
        self.assertFalse(result['unresolved']);self.assertGreaterEqual(len(result['errors']),5)

    def test_cleanup_cancel_exception_preserved(self):
        guard=NS(cancel_owned=lambda:None,finish=lambda **kw:{},check=lambda:None)
        child=NS(pid=12,returncode=None)
        with patch.object(c.os,'wait4',return_value=(12,0,None)),patch.object(c.os,'close'):
            result=c.cleanup(child,99,READY,guard,Mock(side_effect=OSError('cancel')),outer=True)
        self.assertTrue(result['unresolved']);self.assertTrue(any('cancel' in e for e in result['errors']))


class SyntheticTree:
    """Tiny in-memory filesystem: no procfs/systemd/native process observations."""
    def __init__(self,nodes):
        self.nodes=nodes;self.fds={};self.nextfd=100
    def path(self,path,fd=None):
        if isinstance(path,int):return self.fds[path][0]
        if fd is not None:return self.fds[fd][0].rstrip('/')+'/'+str(path)
        return str(path)
    def st(self,path):
        row=self.nodes[path];kind=row[0];raw=row[1] if len(row)>1 else b''
        return NS(st_mode={'dir':0o40755,'file':0o100644,'link':0o120777}[kind],st_uid=1,st_gid=1,
                  st_dev=1,st_ino=list(self.nodes).index(path)+1,st_size=len(raw),st_mtime_ns=1,st_ctime_ns=1,st_nlink=1)
    def open(self,path,flags,dir_fd=None):
        path=self.path(path,dir_fd)
        if path not in self.nodes:raise FileNotFoundError(path)
        if self.nodes[path][0]=='link':raise AssertionError('must resolve aliases explicitly')
        self.nextfd+=1;self.fds[self.nextfd]=[path,0];return self.nextfd
    def stat(self,path,dir_fd=None,follow_symlinks=False):return self.st(self.path(path,dir_fd))
    def fstat(self,fd):return self.st(self.path(fd))
    def readlink(self,path,dir_fd=None):return self.nodes[self.path(path,dir_fd)][1]
    def read(self,fd,n):
        path,off=self.fds[fd];raw=self.nodes[path][1];piece=raw[off:off+n];self.fds[fd][1]+=len(piece);return piece
    def close(self,fd):del self.fds[fd]
    def patches(self):
        import contextlib
        stack=contextlib.ExitStack()
        for key in ('open','stat','fstat','readlink','read','close'):stack.enter_context(patch.object(d.os,key,getattr(self,key)))
        return stack


class Candidate(unittest.TestCase):
    def test_unresolved_roles_are_data(self):
        self.assertEqual(d.data_status(['unknown ELF mapping'],[]),'DATA_WITH_UNRESOLVED_ROLES')
        self.assertEqual(d.data_status([],['failed hash']),'COLLECTION_FAILED')

    def test_full_interval_source_and_chain_drift(self):
        for before,after in [({'sha':'a'},{'sha':'b'}),({'chain':[1]},{'chain':[2]})]:
            with self.assertRaisesRegex(ValueError,'full-interval'):d.stable(before,after)

    def test_expected_source_missing_or_drift(self):
        for pins in [{},{'/x':{'sha256':'b'}}]:
            with self.assertRaises(ValueError):d.verify_expected({'pins':pins},{'/x':'a'})

    def test_finite_stat_before_hash(self):
        a=d.Acquisition(float('inf'))
        st=NS(st_mode=0o100600,st_uid=1,st_gid=1,st_dev=1,st_ino=2,st_size=d.FILE_LIMIT+1,st_mtime_ns=1,st_ctime_ns=1,st_nlink=1)
        with self.assertRaisesRegex(ValueError,'BEFORE hash'):a.record('/usr/bin/x',st)

    def test_alias_resolved_target_admission(self):
        self.assertTrue(d.admit('/usr/lib/python3.12/x'))
        self.assertFalse(d.admit('/etc/shadow'));self.assertFalse(d.admit('/usr/library/x'))

    def test_bootstrap_seal_mismatch(self):
        fake=MagicMock();fake.open.return_value.__enter__.return_value=NS(fileno=lambda:9,read=lambda n:b'{}')
        stage=MagicMock();stage.__truediv__=Mock(return_value=fake)
        with patch.object(d.os,'fstat',return_value=NS(st_size=2,st_dev=1,st_ino=1,st_mode=0o100600,st_uid=1,st_gid=1,st_mtime_ns=1,st_ctime_ns=1,st_nlink=1)),self.assertRaisesRegex(ValueError,'seal drift'):d.bootstrap(stage)

    def test_complete_alias_chain_and_hash(self):
        tree=SyntheticTree({'/':('dir',),'/usr':('dir',),'/usr/bin':('dir',),
                            '/usr/bin/python3':('link','python3.12'),'/usr/bin/python3.12':('file',b'python')})
        with tree.patches():
            a=d.Acquisition(float('inf'));a.add('/usr/bin/python3');snap=a.snapshot()
            self.assertEqual(snap['pins']['/usr/bin/python3']['canonical'],'/usr/bin/python3.12')
            self.assertEqual(snap['pins']['/usr/bin/python3']['sha256'],hashlib.sha256(b'python').hexdigest())
            self.assertEqual(snap['catalog']['entries']['/usr/bin/python3']['target'],'python3.12')
        self.assertFalse(tree.fds)

    def test_alias_cycle_rejected_and_descriptors_closed(self):
        tree=SyntheticTree({'/':('dir',),'/usr':('dir',),'/usr/bin':('dir',),
                            '/usr/bin/a':('link','b'),'/usr/bin/b':('link','a')})
        with tree.patches(),self.assertRaisesRegex(ValueError,'alias cycle'):
            d.Acquisition(float('inf')).add('/usr/bin/a')
        self.assertFalse(tree.fds)

    def test_alias_target_outside_admission_is_data(self):
        tree=SyntheticTree({'/':('dir',),'/usr':('dir',),'/usr/bin':('dir',),'/usr/bin/a':('link','/etc/unknown')})
        with tree.patches():
            a=d.Acquisition(float('inf'));a.add('/usr/bin/a')
        self.assertFalse(a.files);self.assertIn('outside',a.unresolved[0]['reason'])

    def test_interval_metadata_mutation_fails_even_same_bytes(self):
        tree=SyntheticTree({'/':('dir',),'/usr':('dir',),'/usr/bin':('dir',),'/usr/bin/a':('file',b'a')})
        with tree.patches():
            a=d.Acquisition(float('inf'));a.add('/usr/bin/a');a.snapshot()
            old=tree.st
            def changed(path):
                row=old(path)
                if path=='/usr/bin/a':row.st_ctime_ns=2
                return row
            tree.st=changed
            with self.assertRaisesRegex(ValueError,'metadata drift'):a.snapshot()

    def test_verified_scope_removal_and_reuse_refusal(self):
        scope=bound();scope.read=Mock(side_effect=FileNotFoundError(2,'removed'))
        scope.show.return_value=dict(ROW,LoadState='not-found',ActiveState='inactive',InvocationID='',ControlGroup='')
        with patch.object(s.os,'fstat',return_value=NS(st_nlink=0)),patch.object(s.os,'stat',side_effect=FileNotFoundError):
            self.assertTrue(scope.empty())
            scope.show.return_value=dict(ROW,InvocationID='b'*32)
            with self.assertRaises(FileNotFoundError):scope.empty()

    def test_setup_collect_returns_unresolved_data_without_authority(self):
        import FinalNativeGate_setup as setup
        import FinalNativeGate_setup_observe as observation
        import FinalNativeGate_guard as guard_module
        acquisition=Mock();acquisition.files=[];acquisition.unresolved=[]
        acquisition.snapshot.return_value={'pins':{},'catalog':{}}
        guard=Mock();guard.finish.return_value={}
        published={}
        def publish(name,value):published[name]=value;return dict(name=name,size=1,sha256='0'*64)
        plan=dict(files={},native_roots=[],setup_library_search=[],source_revision='synthetic')
        with patch.object(setup,'HERE',setup.STAGE),patch.object(setup,'_inputs',return_value=plan),patch.object(setup,'_guard',return_value=guard),patch.object(setup,'_publish',side_effect=publish),patch.object(setup.signal,'signal'),patch.object(setup.signal,'alarm'),patch.object(s,'environment',return_value=dict(XDG_RUNTIME_DIR='/run/user/123')),patch.dict(setup.os.environ,{'SYNTHETIC':'true'},clear=True),patch.object(d,'Acquisition',return_value=acquisition),patch.object(d,'bootstrap',return_value={}),patch.object(d,'runtime_proposal',return_value=dict(executable='/usr/bin/python3',mapped_libraries=[],stdlib='/usr/lib/python3',maps='synthetic')),patch.object(observation,'collect',return_value={'decision':{'allowed':True}}),patch.object(observation,'controls',return_value={'path':'/'+setup.UNIT+'.scope'}),patch.object(observation,'check_controls'),patch.object(guard_module,'inherited_limits',return_value={}),patch.object(guard_module,'check_limits'):
            self.assertEqual(setup._collect(),0)
        terminal=published['FinalNativeGate-setup-terminal.json']
        self.assertEqual(terminal['status'],'DATA_WITH_UNRESOLVED_ROLES')
        self.assertFalse(terminal['execution_authority'])

    def test_permission_metadata_is_unresolved_data(self):
        tree=SyntheticTree({'/':('dir',),'/usr':('dir',),'/usr/bin':('dir',),'/usr/bin/unsafe':('file',b'x')})
        original=tree.st
        def unsafe(path):
            row=original(path)
            if path=='/usr/bin/unsafe':row.st_mode=0o100666
            return row
        tree.st=unsafe
        with tree.patches():
            a=d.Acquisition(float('inf'));a.add('/usr/bin/unsafe');snap=a.snapshot()
        self.assertFalse(snap['pins']);self.assertTrue(a.unresolved)
        self.assertIn('/usr/bin/unsafe',snap['catalog']['entries'])

    def test_empty_scope_unreadable_terminal_identity_unresolved(self):
        scope=bound();scope.empty=Mock(return_value=True);scope.show.side_effect=PermissionError('metadata')
        with self.assertRaises(PermissionError):scope.finish()

    def test_raw_publication_external_hash_and_size(self):
        import io
        import FinalNativeGate_observe as final
        import FinalNativeGate_setup_observe as setup
        class Output(io.BytesIO):
            def close(self):pass
            def fileno(self):return 9
        for module in (final,setup):
            out=Output();path=MagicMock();path.__truediv__.return_value=path
            path.lstat.return_value=NS(st_mode=0o40700,st_uid=123)
            path.open.return_value.__enter__.return_value=out
            with patch.object(module,'HERE',path),patch.object(module.os,'getuid',return_value=123),patch.object(module.os,'fsync'),patch.object(module.os,'open',return_value=99),patch.object(module.os,'close'):
                receipt=module.save('synthetic.json',{'candidate':'DATA'})
            self.assertEqual(receipt['size'],len(out.getvalue()))
            self.assertEqual(receipt['sha256'],hashlib.sha256(out.getvalue()).hexdigest())
            path.open.assert_called_once_with('xb')

    def test_public_entries_unconditional(self):
        for name in ['FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py']:
            main=next(n for n in ast.parse((HERE/name).read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='main')
            self.assertEqual(len(main.body),2);self.assertEqual(main.body[-1].value.value,78)

if __name__=='__main__':unittest.main(verbosity=2)
