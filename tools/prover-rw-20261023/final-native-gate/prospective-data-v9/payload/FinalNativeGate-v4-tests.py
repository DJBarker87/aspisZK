"""Prospective payload checks. OS/transport replaced; never call actual setup."""
import ast
import base64
import copy
import hashlib
import json
import os
from pathlib import Path
import stat
from types import SimpleNamespace as NS
import unittest
from unittest.mock import Mock,patch

D=Path(__file__).resolve().parent
R=D/'prospective-data-v4'

def receiver():
    ns={'__name__':'source_review_only'}
    exec((R/'FinalNativeGate-data-transfer.py').read_bytes(),ns)
    return ns

class Tree:
    def __init__(self,ns):
        self.nodes={};self.fds={};self.counter=100;self.fail_close=False;self.hardlink=False;self.change_ctime=False
        current=''
        for part in ['',*ns['STAGE'].split('/')[1:-1]]:
            current=(current+'/'+part) if current else '/'
            current=current.replace('//','/')
            self.nodes[current]=dict(mode=0o40755,raw=bytearray(),uid=123)
        self.api=NS(**{k:getattr(os,k) for k in ('O_RDONLY','O_WRONLY','O_DIRECTORY','O_NOFOLLOW','O_NONBLOCK','O_CREAT','O_EXCL')},
            getuid=lambda:123,open=self.open,close=self.close,stat=self.stat,fstat=self.fstat,mkdir=self.mkdir,write=self.write,read=self.read,fsync=lambda fd:None)
    def path(self,name,dir_fd=None):
        if dir_fd is None:return str(name)
        return self.fds[dir_fd][0].rstrip('/')+'/'+name
    def stat(self,name,dir_fd=None,follow_symlinks=False):
        path=self.path(name,dir_fd)
        if path not in self.nodes:raise FileNotFoundError(path)
        row=self.nodes[path]
        return NS(st_dev=1,st_ino=list(self.nodes).index(path)+1,st_mode=row['mode'],st_uid=row['uid'],st_gid=123,
            st_size=len(row['raw']),st_mtime_ns=1,st_ctime_ns=row.get('ctime',1),st_atime_ns=row.get('atime',1),st_nlink=2 if self.hardlink and stat.S_ISREG(row['mode']) else 1)
    def fstat(self,fd):return self.stat(self.fds[fd][0])
    def open(self,name,flags,mode=0o777,dir_fd=None):
        path=self.path(name,dir_fd)
        if not flags&os.O_NOFOLLOW:raise AssertionError('missing nofollow')
        if flags&os.O_CREAT:
            if path in self.nodes:raise FileExistsError(path)
            if not flags&os.O_EXCL:raise AssertionError('missing exclusive')
            self.nodes[path]=dict(mode=stat.S_IFREG|mode,raw=bytearray(),uid=123)
        if path not in self.nodes:raise FileNotFoundError(path)
        if stat.S_ISLNK(self.nodes[path]['mode']):raise OSError('symlink')
        self.counter+=1;self.fds[self.counter]=[path,0,bool(flags&os.O_WRONLY)]
        return self.counter
    def close(self,fd):
        path,offset,writer=self.fds.pop(fd)
        if writer and self.fail_close:self.nodes[path]['raw'][:1]=b'!'
    def mkdir(self,name,mode,dir_fd):
        path=self.path(name,dir_fd)
        if path in self.nodes:raise FileExistsError(path)
        self.nodes[path]=dict(mode=stat.S_IFDIR|mode,raw=bytearray(),uid=123)
    def write(self,fd,raw):self.nodes[self.fds[fd][0]]['raw'].extend(raw);return len(raw)
    def read(self,fd,n):
        path,at,_=self.fds[fd]
        self.nodes[path]['atime']=self.nodes[path].get('atime',1)+1
        if self.change_ctime:self.nodes[path]['ctime']=self.nodes[path].get('ctime',1)+1
        raw=bytes(self.nodes[path]['raw'][at:at+n]);self.fds[fd][1]+=len(raw);return raw

class Release(unittest.TestCase):
    def test_exact_activated_bytes_seals_and_only_two_entry_deltas(self):
        ns=receiver();rows=ns['decoded']();ns['verify'](rows)
        identity=json.loads((R/'FinalNativeGate-release-identities.json').read_bytes())
        for name,raw in rows.items():self.assertEqual(raw,(R/'payload'/name).read_bytes())
        for name in ('FinalNativeGate.py','FinalNativeGate_inside.py'):
            self.assertEqual(rows[name],(D/name).read_bytes())
        for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
            main=next(n for n in ast.parse((D/name).read_bytes()).body if isinstance(n,ast.FunctionDef) and n.name=='main')
            self.assertEqual(len(main.body),2);self.assertEqual(main.body[-1].value.value,78)
        for name,row in identity['function_identities'].items():
            self.assertEqual(row['changed'],['main'] if name in ('FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py') else [])
        self.assertTrue(identity['no_final_charge_authority'])
        p=json.loads(rows['FinalNativeGate-plan.json']);original=json.loads((D/'FinalNativeGate-plan.json').read_bytes())
        stage=ns['STAGE']+'/'
        self.assertEqual({k:v for k,v in p['files'].items() if not k.startswith(stage)},
                         {k:v for k,v in original['files'].items() if not k.startswith(stage)})
        for key in p:
            if key not in ('files','job_source_sizes','job_revision','setup_catalog_roots'):self.assertEqual(p[key],original[key],key)

    def test_receiver_exclusive_copy_closed_writer_and_packet_creation(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        result=ns['install']();self.assertFalse(tree.fds)
        self.assertEqual(result['status'],'FIXED_DATA_SOURCE_TRANSFERRED')
        self.assertFalse(result['execution_authority'])
        for name,raw in ns['decoded']().items():
            row=tree.nodes[ns['STAGE']+'/'+name];self.assertEqual(bytes(row['raw']),raw);self.assertEqual(row['mode'],0o100600)
        # Packet directory changes no code-file bytes/identities.
        before={n:bytes(v['raw']) for n,v in tree.nodes.items() if stat.S_ISREG(v['mode'])}
        fd=tree.open(ns['STAGE'],os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        tree.mkdir('FinalNativeGate-setup-packet',0o700,fd);tree.close(fd)
        self.assertEqual(before,{n:bytes(tree.nodes[n]['raw']) for n in before})
        with self.assertRaises(FileExistsError):ns['install']()
        self.assertFalse(tree.fds)

    def test_receiver_ancestry_alias_refused(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        tree.nodes['/home']['mode']=0o120777
        with self.assertRaisesRegex(ValueError,'ancestor'):ns['install']()
        self.assertNotIn(ns['STAGE'],tree.nodes);self.assertFalse(tree.fds)

    def test_receiver_wrong_parent_owner_refused(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        tree.nodes[ns['STAGE'].rsplit('/',1)[0]]['uid']=0
        with self.assertRaisesRegex(ValueError,'user owned'):ns['install']()
        self.assertNotIn(ns['STAGE'],tree.nodes)

    def test_receiver_failed_closed_writer_hash_retains_partial(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api;tree.fail_close=True
        with self.assertRaisesRegex(ValueError,'source drift'):ns['install']()
        self.assertIn(ns['STAGE'],tree.nodes)
        self.assertTrue(any(n.startswith(ns['STAGE']+'/') for n in tree.nodes));self.assertFalse(tree.fds)

    def test_receiver_hardlink_refused_retains_partial(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api;tree.hardlink=True
        with self.assertRaisesRegex(ValueError,'single-link'):ns['install']()
        self.assertIn(ns['STAGE'],tree.nodes);self.assertFalse(tree.fds)

    def test_receiver_pinned_bytes_and_seal_corruption_rejected(self):
        ns=receiver();rows=ns['decoded']();rows['FinalNativeGate_seal.py']=b'wrong'
        with self.assertRaisesRegex(ValueError,'plan seal'):ns['verify'](rows)
        first=next(iter(ns['FILES']));ns['FILES'][first]['b85']=base64.b85encode(b'bad').decode()
        with self.assertRaisesRegex(ValueError,'pinned bytes'):ns['decoded']()

    def test_receiver_limits_before_decode_or_write(self):
        ns=receiver();first=next(iter(ns['FILES']));ns['FILES'][first]['size']=4*2**20+1
        with self.assertRaisesRegex(ValueError,'per-file bound'):ns['decoded']()

    def packet(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        ns['install']()
        fd=tree.open(ns['STAGE'],os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        tree.mkdir('FinalNativeGate-setup-packet',0o700,fd);tree.close(fd)
        for name in ('FinalNativeGate-setup-terminal.json','FinalNativeGate-setup-parent-terminal.json',
                     'FinalNativeGate-candidate-controls.json','FinalNativeGate-setup-parent-cleanup.json','FinalNativeGate-setup-parent-guard.json'):
            tree.nodes[ns['STAGE']+'/FinalNativeGate-setup-packet/'+name]=dict(mode=0o100600,raw=bytearray(json.dumps({'role':name,'execution_authority':False}).encode()),uid=123)
        return ns,tree

    def test_fixed_packet_summary_public_records_and_hash_only_cleanup(self):
        ns,tree=self.packet();summary=ns['packet_summary']()
        self.assertEqual(len(summary),5)
        self.assertEqual(summary['FinalNativeGate-candidate-controls.json']['record']['role'],'FinalNativeGate-candidate-controls.json')
        self.assertNotIn('record',summary['FinalNativeGate-setup-parent-cleanup.json'])
        for name,row in summary.items():
            raw=bytes(tree.nodes[ns['STAGE']+'/FinalNativeGate-setup-packet/'+name]['raw'])
            self.assertEqual(row['sha256'],hashlib.sha256(raw).hexdigest());self.assertEqual(row['size'],len(raw))
        self.assertFalse(tree.fds)

    def test_fixed_packet_missing_file_exact_partial_error(self):
        ns,tree=self.packet()
        del tree.nodes[ns['STAGE']+'/FinalNativeGate-setup-packet/FinalNativeGate-candidate-controls.json']
        summary=ns['packet_summary']()
        self.assertIn('FinalNativeGate-candidate-controls.json',summary['FinalNativeGate-candidate-controls.json']['error'])
        self.assertIn('record',summary['FinalNativeGate-setup-terminal.json']);self.assertFalse(tree.fds)

    def test_packet_alias_refused(self):
        ns,tree=self.packet();tree.nodes[ns['STAGE']+'/FinalNativeGate-setup-packet']['mode']=0o120777
        with self.assertRaisesRegex(ValueError,'ancestor'):ns['packet_summary']()
        self.assertFalse(tree.fds)

    def test_receiver_ctime_change_rejected_even_with_identical_bytes(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api;tree.change_ctime=True
        with self.assertRaisesRegex(ValueError,'source drift'):ns['install']()
        self.assertIn(ns['STAGE'],tree.nodes);self.assertFalse(tree.fds)

    def test_source_stamp_excludes_only_atime_not_content_identity(self):
        ns=receiver()
        first=NS(st_dev=1,st_ino=2,st_mode=0o100600,st_uid=123,st_gid=123,st_size=4,st_mtime_ns=10,st_ctime_ns=11,st_nlink=1,st_atime_ns=1)
        after=copy.copy(first);after.st_atime_ns=99
        self.assertEqual(ns['source_stamp'](first),ns['source_stamp'](after))
        after.st_ctime_ns=12
        self.assertNotEqual(ns['source_stamp'](first),ns['source_stamp'](after))

    def test_literal_outer_transport_without_execution(self):
        ns={'__name__':'source_review_only'}
        exec((R/'FinalNativeGate-data-transport.py').read_bytes(),ns)
        self.assertEqual(ns['ARGV'][-2:],['dombarker@100.108.41.90','/usr/bin/python3 -I -B -'])
        self.assertEqual(ns['PIN']['sha256'],hashlib.sha256((R/'FinalNativeGate-data-transfer.py').read_bytes()).hexdigest())
        text=(R/'FinalNativeGate-data-transport.py').read_text()
        self.assertIn('>120',text);self.assertEqual(ns['LIMIT'],4*2**20)
        self.assertNotIn('shell=True',text)
        # Only receiver main may launch setup; no final call in receiver AST.
        calls=[n for n in ast.walk(ast.parse((R/'FinalNativeGate-data-transfer.py').read_bytes())) if isinstance(n,ast.Call)]
        self.assertFalse(any(isinstance(n.func,ast.Name) and n.func.id in ('_execute','_charge') for n in calls))

class PathRepair(unittest.TestCase):
    def test_fixed_literal_path_and_nonstage_roots(self):
        ns=receiver();self.assertEqual(ns['STAGE'],'/home/dombarker/final-native-gate')
        rows=ns['decoded']();p=json.loads(rows['FinalNativeGate-plan.json'])
        old='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate'
        for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py','FinalNativeGate_scope.py'):
            self.assertNotIn(old,rows[name].decode())
            self.assertIn(ns['STAGE'],rows[name].decode())
        self.assertFalse(any(k.startswith(old+'/') for k in p['files']))
        self.assertEqual(set(p['job_source_sizes']),{ns['STAGE']+'/'+n for n in rows if n.endswith('.py') and n not in ('FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py')})
        # Retained immutable Git inputs, never read another live worktree/cache.
        import subprocess
        path='tools/prover-rw-20261023/final-native-gate/FinalNativeGate-plan.json'
        original=json.loads(subprocess.check_output(['git','show','c67d0a3d5a:'+path]))
        self.assertEqual({k:v for k,v in original['files'].items() if not k.startswith(old+'/')},
                         {k:v for k,v in p['files'].items() if not k.startswith(ns['STAGE']+'/')})
        for key in p:
            if key not in ('files','job_source_sizes','job_revision','setup_catalog_roots'):self.assertEqual(p[key],original[key],key)
        self.assertIn("base='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/'",rows['FinalNativeGate_setup.py'].decode())
        self.assertIn('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/resume-scalar/proof/Cargo.toml',rows['FinalNativeGate.py'].decode())

    def test_fresh_0775_ancestor_denied_and_secure_0750_accepted(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        tree.nodes['/home/dombarker']['mode']=0o40775
        with self.assertRaisesRegex(ValueError,'ancestor'):ns['install']()
        self.assertNotIn(ns['STAGE'],tree.nodes);self.assertFalse(tree.fds)
        tree.nodes['/home/dombarker']['mode']=0o40750
        self.assertEqual(ns['install']()['status'],'FIXED_DATA_SOURCE_TRANSFERRED');self.assertFalse(tree.fds)

    def test_preexisting_directory_regular_and_dangling_alias_denied(self):
        for mode in (0o40700,0o100600,0o120777):
            with self.subTest(mode=mode):
                ns=receiver();tree=Tree(ns);ns['os']=tree.api
                tree.nodes[ns['STAGE']]=dict(mode=mode,raw=bytearray(b'retain'),uid=123)
                before=copy.deepcopy(tree.nodes)
                with self.assertRaises(FileExistsError):ns['install']()
                self.assertEqual(tree.nodes,before);self.assertFalse(tree.fds)

    def test_exact_coverage_and_manifest_tamper_denied(self):
        ns=receiver();rows=ns['decoded']();rows.pop('FinalNativeGate-fixtures.py')
        with self.assertRaisesRegex(ValueError,'coverage'):ns['verify'](rows)
        ns=receiver();ns['TRANSFER_ROOT_SHA256']='0'*64
        with self.assertRaisesRegex(ValueError,'manifest root'):ns['decoded']()

class ParentTerminal(unittest.TestCase):
    def run_parent(self,fault=None,child_status=0,unresolved=False,historical=False):
        import contextlib,io,fcntl,subprocess
        from unittest.mock import mock_open
        import FinalNativeGate_setup as setup
        import FinalNativeGate_scope as scope
        import FinalNativeGate_candidate as candidate
        import FinalNativeGate_cleanup as cleanup
        import FinalNativeGate_guard as guard_module
        import FinalNativeGate_setup_observe as observe
        if historical:
            import subprocess,types
            raw=subprocess.check_output(['git','show','c67d0a3d5a:tools/prover-rw-20261023/final-native-gate/FinalNativeGate_setup.py'])
            setup=types.ModuleType('retained_prior_setup');setup.__file__=str(D/'FinalNativeGate_setup.py')
            exec(raw,setup.__dict__)
        published={};order=[];guard=Mock();child=NS(pid=4242,returncode=None)
        closure=dict(errors=['SCOPE_UNRESOLVED'] if unresolved else [],monitor={'retained':'telemetry'},unresolved=unresolved)
        def publish(name,value):
            order.append(name)
            if name==fault:raise OSError('synthetic prior receipt write fault')
            published[name]=copy.deepcopy(value)
        with contextlib.ExitStack() as stack:
            bindings=[(setup,'HERE',setup.STAGE),(setup,'_inputs',lambda:{}),(setup,'_guard',lambda:guard),(setup,'_publish',publish),
                (setup.signal,'signal',Mock()),(Path,'mkdir',Mock()),(Path,'open',mock_open()),
                (scope,'FixedScope',lambda kind:Mock()),(scope,'environment',lambda:{}),
                (observe,'collect',lambda phase:{'decision':{'allowed':True}}),
                (candidate,'bootstrap',lambda stage:{}),(candidate,'stable',Mock()),
                (cleanup,'cleanup',lambda *a,**kw:copy.deepcopy(closure)),
                (guard_module,'Proc',lambda:Mock()),(subprocess,'Popen',lambda *a,**kw:child),
                (setup.os,'wait4',lambda *a:(4242,child_status<<8,None)),(fcntl,'flock',Mock())]
            for obj,key,value in bindings:stack.enter_context(patch.object(obj,key,value))
            stack.enter_context(patch.object(setup.os,'pidfd_open',lambda pid:99,create=True))
            stack.enter_context(patch('builtins.open',mock_open()))
            code=setup._prospective()
        return code,published,order

    def test_retained_historical_counterexample(self):
        code,published,_=self.run_parent('FinalNativeGate-setup-parent-cleanup.json',historical=True)
        self.assertEqual(code,78)
        self.assertFalse(published['FinalNativeGate-setup-parent-terminal.json']['failed'])
        self.assertTrue(published['FinalNativeGate-setup-parent-terminal.json']['errors'])

    def test_prior_write_fault_persisted_terminal_is_failed(self):
        for fault in ('FinalNativeGate-setup-parent-cleanup.json','FinalNativeGate-setup-parent-guard.json'):
            with self.subTest(fault=fault):
                code,published,order=self.run_parent(fault)
                self.assertEqual(code,78)
                terminal=published['FinalNativeGate-setup-parent-terminal.json']
                self.assertTrue(terminal['failed']);self.assertIn(fault,terminal['errors'][0])
                self.assertEqual(order[-1],'FinalNativeGate-setup-parent-terminal.json')
                self.assertFalse(terminal['execution_authority'])

    def test_terminal_write_fault_nonzero_and_no_forged_terminal(self):
        code,published,_=self.run_parent('FinalNativeGate-setup-parent-terminal.json')
        self.assertEqual(code,78);self.assertNotIn('FinalNativeGate-setup-parent-terminal.json',published)

    def test_success_nonzero_child_and_unresolved_retained(self):
        for status,unresolved in ((0,False),(1,False),(0,True)):
            code,published,_=self.run_parent(child_status=status,unresolved=unresolved)
            terminal=published['FinalNativeGate-setup-parent-terminal.json']
            self.assertEqual(code,78 if status or unresolved else 0)
            self.assertEqual(terminal['failed'],bool(status or unresolved))
            self.assertEqual(terminal['unresolved'],unresolved)
            self.assertEqual(published['FinalNativeGate-setup-parent-guard.json'],{'retained':'telemetry'})

if __name__=='__main__':unittest.main(verbosity=2)

