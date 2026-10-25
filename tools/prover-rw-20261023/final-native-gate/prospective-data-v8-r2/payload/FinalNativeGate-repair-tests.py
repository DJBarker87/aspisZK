"""Focused explicit mocks/data only. No native or host operations permitted."""
import contextlib
import copy
import importlib.util
import io
import os
from pathlib import Path
import stat
import sys
import types
import unittest
from unittest.mock import patch,MagicMock

D=Path(__file__).resolve().parent
sys.path.insert(0,str(D))
import FinalNativeGate as job
import FinalNativeGate_bounded as bounded
import FinalNativeGate_cleanup as closing
import FinalNativeGate_setup as setup
import FinalNativeGate_setup_adapter as meta
import FinalNativeGate_adapter as final
import FinalNativeGate_policy as policy

spec=importlib.util.spec_from_file_location('FinalNativeGate_old_fixtures',D/'FinalNativeGate-tests.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)


class FS:
    """Only synthetic /sealed entries; all os boundaries replaced."""
    def __init__(self):
        self.content={'/sealed/data':b'abc'};self.links={};self.handles={};self.next=10
        self.rows={'/':self.node(stat.S_IFDIR|0o755,1),'/sealed':self.node(stat.S_IFDIR|0o700,2),'/sealed/data':self.node(stat.S_IFREG|0o600,3,3)}
        self.names={'/sealed':['data']}
    def node(self,mode,ino,size=0):
        return types.SimpleNamespace(st_dev=1,st_ino=ino,st_mode=mode,st_uid=501,st_gid=20,st_size=size,st_mtime_ns=1,st_ctime_ns=1,st_nlink=1)
    def path(self,name,dir_fd=None):
        if name.startswith('/'):return name
        return self.handles[dir_fd][0].rstrip('/')+'/'+name
    def open(self,name,flags,dir_fd=None):
        path=self.path(name,dir_fd);self.next+=1;self.handles[self.next]=[path,0];return self.next
    def stat(self,name,dir_fd=None,follow_symlinks=False):return copy.copy(self.rows[self.path(name,dir_fd)])
    def fstat(self,fd):return copy.copy(self.rows[self.handles[fd][0]])
    def read(self,fd,n):
        path,offset=self.handles[fd];data=self.content[path][offset:offset+n];self.handles[fd][1]+=len(data);return data
    def pread(self,fd,n,off):return self.content[self.handles[fd][0]][off:off+n]
    @contextlib.contextmanager
    def scandir(self,fd):yield iter(types.SimpleNamespace(name=n) for n in self.names[self.handles[fd][0]])
    def catalog(self):
        entries={p:dict(kind='dir' if stat.S_ISDIR(s.st_mode) else 'link' if stat.S_ISLNK(s.st_mode) else 'file',uid=s.st_uid,gid=s.st_gid,mode=s.st_mode,**({'size':s.st_size} if stat.S_ISREG(s.st_mode) else {})) for p,s in self.rows.items()}
        entries['/sealed']['children']=self.names['/sealed'].copy()
        for p,target in self.links.items():entries[p]['target']=target
        return dict(entries=entries,roots=['/sealed'],bounds=dict(files=len(entries)+2,bytes=10,seconds=115),rationale='tiny explicit fixture')
    @contextlib.contextmanager
    def mocked(self):
        with patch.multiple(os,open=self.open,stat=self.stat,fstat=self.fstat,read=self.read,pread=self.pread,close=lambda fd:None,scandir=self.scandir,readlink=lambda name,dir_fd=None:self.links[self.path(name,dir_fd)]):yield


class BoundedInputs(unittest.TestCase):
    def test_exact_inventory_and_streamed_size(self):
        fs=FS();c=fs.catalog()
        with fs.mocked():
            result=bounded.Reader(c).inventory(['/sealed'])
        self.assertEqual(result['/sealed/data']['size'],3)
    def test_source_pin_inventory_coverage(self):
        import hashlib
        fs=FS();c=fs.catalog();expected={'/sealed/data':hashlib.sha256(b'abc').hexdigest()}
        with fs.mocked():
            self.assertEqual(job._file_pins(dict(catalogs={'source':c},files=expected)),expected)
            with self.assertRaisesRegex(job.Denied,'coverage'):job._file_pins(dict(catalogs={'source':c},files={}))
    def test_unknown_membership_denies(self):
        fs=FS();c=fs.catalog();fs.names['/sealed'].append('unknown')
        with fs.mocked(),self.assertRaisesRegex(ValueError,'unknown directory'):bounded.Reader(c).inventory(['/sealed'])
    def test_size_growth_denies_before_read(self):
        fs=FS();c=fs.catalog();fs.rows['/sealed/data'].st_size=4
        with fs.mocked(),self.assertRaisesRegex(ValueError,'planned size'):bounded.Reader(c).pin('/sealed/data')
    def test_stream_growth_and_short_read(self):
        for raw in (b'abcd',b'ab'):
            fs=FS();c=fs.catalog();fs.content['/sealed/data']=raw
            with fs.mocked(),self.assertRaises(ValueError):bounded.Reader(c).pin('/sealed/data')
    def test_fd_post_metadata_change(self):
        fs=FS();c=fs.catalog();read=fs.read
        def mutate(fd,n):
            raw=read(fd,n);fs.rows['/sealed/data'].st_ctime_ns=2;return raw
        with fs.mocked(),patch.object(os,'read',mutate),self.assertRaisesRegex(ValueError,'changed during read'):bounded.Reader(c).pin('/sealed/data')
    def test_approved_alias_and_cycle(self):
        fs=FS();fs.rows['/sealed/alias']=fs.node(stat.S_IFLNK|0o777,4);fs.links['/sealed/alias']='data';c=fs.catalog()
        # Symlink777 is metadata, not writable target contents; explicit policy.
        with fs.mocked():self.assertEqual(bounded.Reader(c).pin('/sealed/alias')['canonical'],'/sealed/data')
        fs.links['/sealed/alias']='alias';c=fs.catalog()
        with fs.mocked(),self.assertRaisesRegex(ValueError,'cycle'):bounded.Reader(c).pin('/sealed/alias')
    def test_unapproved_chain_escape(self):
        fs=FS();fs.rows['/sealed/alias']=fs.node(stat.S_IFLNK|0o777,4);fs.links['/sealed/alias']='/outside/private';c=fs.catalog()
        with fs.mocked(),self.assertRaisesRegex(ValueError,'unknown chain'):bounded.Reader(c).pin('/sealed/alias')
    def test_bytes_time_owner_mode_bounds(self):
        for kind in ('bytes','time','uid','mode'):
            fs=FS();c=fs.catalog()
            if kind=='bytes':c['bounds']['bytes']=2
            if kind=='uid':fs.rows['/sealed/data'].st_uid=0
            if kind=='mode':fs.rows['/sealed/data'].st_mode|=0o020
            with fs.mocked():
                r=bounded.Reader(c)
                if kind=='time':r.deadline=-1
                with self.assertRaises(ValueError):r.pin('/sealed/data')
    def test_no_catalog_no_fallback(self):
        with self.assertRaises(ValueError):bounded.Reader(None)


class CatalogAndELF(unittest.TestCase):
    def test_discovery_records_alias_without_following(self):
        from FinalNativeGate_catalog import discover
        fs=FS();fs.rows['/sealed/alias']=fs.node(stat.S_IFLNK|0o777,4)
        fs.links['/sealed/alias']='/private/never-read';fs.names['/sealed'].append('alias')
        with fs.mocked():catalog,missing=discover(['/sealed'],8,10**20)
        self.assertTrue(missing);self.assertEqual(catalog['entries']['/sealed/alias']['target'],'/private/never-read')
        self.assertFalse(any(p.startswith('/private') for p,_ in fs.handles.values()))
    def test_discovery_entry_bound(self):
        from FinalNativeGate_catalog import discover
        fs=FS()
        with fs.mocked(),self.assertRaisesRegex(ValueError,'envelope'):discover(['/sealed'],2,10**20)
    def test_synthetic_elf_interpreter_and_needed(self):
        import struct
        from FinalNativeGate_elf import dependencies
        fs=FS();raw=bytearray(1024);raw[:6]=b'\x7fELF\x02\x01'
        struct.pack_into('<H',raw,18,62);struct.pack_into('<Q',raw,32,64);struct.pack_into('<HH',raw,54,56,3)
        struct.pack_into('<IIQQQQQQ',raw,64,1,0,0,0,0,1024,1024,1)
        struct.pack_into('<IIQQQQQQ',raw,120,3,0,240,240,0,8,8,1)
        struct.pack_into('<IIQQQQQQ',raw,176,2,0,256,256,0,64,64,8)
        raw[240:248]=b'/loader\0'
        for off,tag,val in [(256,5,512),(272,10,11),(288,1,1),(304,0,0)]:struct.pack_into('<qQ',raw,off,tag,val)
        raw[512:523]=b'\0libc.so.6\0'
        fs.content['/sealed/data']=bytes(raw);fs.rows['/sealed/data'].st_size=len(raw);c=fs.catalog();c['bounds']['bytes']=1024
        with fs.mocked():result=dependencies(bounded.Reader(c),'/sealed/data')
        self.assertEqual(result['interpreter'],['/loader']);self.assertEqual(result['needed'],['libc.so.6'])
    def test_elf_malformed_range_denies(self):
        from FinalNativeGate_elf import dependencies
        fs=FS();fs.content['/sealed/data']=b'\x7fELF';fs.rows['/sealed/data'].st_size=4
        with fs.mocked(),self.assertRaises(ValueError):dependencies(bounded.Reader(fs.catalog()),'/sealed/data')


class Cleanup(unittest.TestCase):
    def test_each_action_independent_and_metrics_null(self):
        for failure in ('cancel','descendants','finish','reap','close','check'):
            child=types.SimpleNamespace(pid=43,returncode=None);guard=MagicMock()
            guard.finish.return_value={'error':None}
            cancel=MagicMock(side_effect=OSError('cancel') if failure=='cancel' else None)
            if failure in ('descendants','finish','check'):
                getattr(guard,{'descendants':'cancel_owned','finish':'finish','check':'check'}[failure]).side_effect=OSError(failure)
            with patch('os.wait4',side_effect=ChildProcessError('reap') if failure=='reap' else [(43,0,None)]),patch('os.close',side_effect=OSError('close') if failure=='close' else None):
                result=closing.cleanup(child,999,{},guard,cancel)
            guard.cancel_owned.assert_called_once();guard.finish.assert_called_once();guard.check.assert_called_once()
            self.assertTrue(result['errors']);self.assertTrue(result['unresolved']);self.assertIsNone(result['usage'])
    def test_future_orphan_after_wrapper_exit_unresolved(self):
        guard=MagicMock();guard.finish.return_value={'error':None}
        result=closing.cleanup(types.SimpleNamespace(pid=43,returncode=0),None,None,guard,MagicMock())
        guard.cancel_owned.assert_called_once();self.assertTrue(result['unresolved'])
    def test_parent_lead_counterexample_terminal_survives(self):
        guard=MagicMock();guard.finish.return_value={'error':None}
        guard.check.side_effect=[None,OSError('monitor failure'),OSError('monitor remains failed')]
        store=old.Store();packet=MagicMock();packet.__truediv__.side_effect=lambda name:old.MemPath(store,name)
        child=types.SimpleNamespace(pid=43,returncode=None)
        with patch.object(job,'HERE',job.STAGE),patch.object(job,'PACKET',packet),patch.object(job,'_plan',return_value={'environment':{},'inherited_limits':{}}),patch.object(job,'_modules',return_value=(old.obs,lambda:guard,lambda:{},lambda *a:None,old.FakeProc)),patch.object(job,'_pins',return_value={}),patch.object(job,'_admit'),patch.object(job,'_save',side_effect=store.save),patch.object(job,'_scope_argv',return_value=['fixed mock argv']),patch.object(job,'_cancel_child',side_effect=OSError('lead cancellation counterexample')),patch('builtins.open',MagicMock()),patch('fcntl.flock'),patch('os.fstat',return_value=types.SimpleNamespace(st_ino=5)),patch('os.pidfd_open',return_value=999,create=True),patch('os.close'),patch('os.wait4',return_value=(43,0,None)),patch('subprocess.Popen',return_value=child),patch('signal.signal'):
            self.assertEqual(job._prospective(),78)
        guard.cancel_owned.assert_called_once();guard.finish.assert_called_once()
        terminal=store.records['FinalNativeGate-parent-terminal.json']
        self.assertTrue(terminal['failed']);self.assertTrue(any('lead cancellation' in x for x in terminal['errors']))
    def test_control_read_error_after_spawn_retains_terminal(self):
        fixture=old.Integration('test_reap_failure_honest');fixture.setUp()
        try:
            fixture.use('FinalNativeGate._controls',side_effect=[{}, {}, {}, OSError('control read failure')])
            self.assertEqual(job._execute(),78)
            self.assertTrue(fixture.store.records['FinalNativeGate-terminal.json']['errors'])
            self.assertIn('FinalNativeGate-guard.json',fixture.store.records)
        finally:fixture.doCleanups()


class SetupIntegration(unittest.TestCase):
    def test_full_1g_policy_inside_counts_once(self):
        env={'c':meta.c,'G':2**30}
        policy.functions(policy.load_bundle()['fixtures']['source'],['node','fixture','legacy','scope'],env)
        snapshot,_=env['scope'](high=768*2**20,cap=2**30)
        for row in snapshot['rows']:
            for key in ('path','parent','owner','domain'):
                if isinstance(row.get(key),str):row[key]=row[key].replace('job.scope',meta.UNIT+'.scope')
        for key in ('path','unified_path'):snapshot['self_observation'][key]=snapshot['self_observation'][key].replace('job.scope',meta.UNIT+'.scope')
        with patch.object(meta,'visibility',return_value=env['legacy'](snapshot,0)),patch.dict(meta.identity,scan_bound=lambda:copy.deepcopy(snapshot)):
            report=meta.read_only_admission(phase='inside-scope')
        self.assertTrue(report['decision']['allowed']);self.assertEqual(report['decision']['requested_bytes'],0)
        self.assertEqual(report['decision']['projected_reserved_bytes'],2**30)
    def test_1g_adapter_diff_is_only_profile_and_unit(self):
        expected=(D/'FinalNativeGate_adapter.py').read_text().replace('high=3*c.GIB,cap=4*c.GIB','high=768*2**20,cap=c.GIB').replace("UNIT='FinalNativeGate-060'","UNIT='FinalNativeGate-pin-setup'").replace('requested=4*c.GIB if','requested=c.GIB if')
        self.assertEqual(expected,(D/'FinalNativeGate_setup_adapter.py').read_text())
    def test_all_public_entries_disabled(self):
        import ast
        for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
            node=next(n for n in ast.parse((D/name).read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='main')
            self.assertEqual(len(node.body),2);self.assertEqual(node.body[1].value.value,78)
    def test_guard_fixed_512m_without_start(self):
        guard=setup._guard();self.assertEqual(guard.budget,512*2**20);self.assertEqual(guard.max_samples,6000)


if __name__=='__main__':
    # All native launch/read-only visibility calls must have an explicit per-test
    # override. No compiler/host/Kani/process can escape a fixture.
    with patch('subprocess.Popen',side_effect=AssertionError('unmocked native process')),patch('subprocess.run',side_effect=AssertionError('unmocked host visibility')):
        unittest.main()
