"""Tiny explicit mocks/source bytes only. No host, setup or native execution."""
import ast
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
from types import SimpleNamespace as NS
import unittest
from unittest.mock import Mock,patch
import FinalNativeGate_setup as setup
import FinalNativeGate_candidate as candidate
import FinalNativeGate_setup_observe as observation
import FinalNativeGate_guard as guard_module
import FinalNativeGate_scope as scope

D=Path(__file__).resolve().parent

class Order(unittest.TestCase):
    def collect(self,deny=None,control_error=False,missing=False):
        trace=[];published={};phase=None
        def mark(name,value=None):
            trace.append(name);return value
        def admission(value):
            nonlocal phase
            phase=value
            return mark(value,{'decision':{'allowed':value!=deny}})
        def control():return mark('controls:'+phase,{'path':'/'+setup.UNIT+'.scope'})
        def check(value):
            mark('check:'+phase)
            if control_error:raise ValueError('synthetic control denial')
        a=Mock();a.files=set();a.unresolved=[]
        a.add.side_effect=lambda *args,**kw:mark('add:'+args[0])
        a.snapshot.side_effect=lambda:mark('snapshot',{'pins':{},'catalog':{}})
        a.catalog.return_value={}
        guard=Mock();guard.start.side_effect=lambda:mark('guard-start');guard.finish.return_value={}
        def publish(name,value):
            published[name]=value;mark('publish:'+name);return dict(name=name,size=1,sha256='0'*64)
        plan=dict(files={'/usr/bin/missing':'a'} if missing else {},native_roots=[],setup_library_search=[],source_revision='synthetic')
        with contextlib.ExitStack() as stack:
            for obj,key,value in [(setup,'HERE',setup.STAGE),(setup,'_inputs',lambda:plan),(setup,'_guard',lambda:guard),(setup,'_publish',publish),
                (setup.signal,'signal',Mock()),(setup.signal,'alarm',Mock()),
                (scope,'environment',lambda:mark('environment',dict(XDG_RUNTIME_DIR='/run/user/123'))),
                (candidate,'Acquisition',lambda deadline:mark('Acquisition',a)),(candidate,'bootstrap',lambda stage:mark('bootstrap',{})),
                (candidate,'runtime_proposal',lambda:mark('runtime',dict(executable='/usr/bin/python3',mapped_libraries=[],stdlib='/usr/lib/python3',maps='mock'))),
                (observation,'collect',admission),(observation,'controls',control),(observation,'check_controls',check),
                (guard_module,'inherited_limits',lambda:{}),(guard_module,'check_limits',Mock())]:
                stack.enter_context(patch.object(obj,key,value))
            status=setup._collect()
        return status,trace,published

    def test_actual_source_positive_order(self):
        status,trace,published=self.collect()
        self.assertEqual(status,0)
        ordered=['guard-start','bootstrap','inside-scope','controls:inside-scope','check:inside-scope','Acquisition','runtime','environment','add:/run/user/123','snapshot','go','controls:go','check:go','snapshot','runtime','bootstrap','publish:FinalNativeGate-candidate-catalog.json']
        cursor=0
        for item in ordered:cursor=trace.index(item,cursor)+1
        self.assertEqual([x for x in trace if x in ('inside-scope','go')],['inside-scope','go'])
        self.assertFalse(published['FinalNativeGate-setup-terminal.json']['execution_authority'])

    def test_denied_inside_no_candidate_discovery(self):
        status,trace,published=self.collect(deny='inside-scope')
        self.assertEqual(status,78)
        self.assertFalse(any(x in ('Acquisition','runtime','environment','snapshot','go') or x.startswith('add:') for x in trace))
        self.assertFalse(any(n.startswith('FinalNativeGate-candidate-') for n in published))
        self.assertEqual(published['FinalNativeGate-setup-terminal.json']['status'],'COLLECTION_FAILED')

    def test_denied_inside_controls_no_candidate_discovery(self):
        status,trace,published=self.collect(control_error=True)
        self.assertEqual(status,78);self.assertNotIn('Acquisition',trace);self.assertNotIn('runtime',trace)

    def test_denied_go_no_final_candidate_publication(self):
        status,trace,published=self.collect(deny='go')
        self.assertEqual(status,78);self.assertIn('snapshot',trace)
        self.assertIn('FinalNativeGate-candidate-partial-failure.json',published)
        self.assertNotIn('FinalNativeGate-candidate-catalog.json',published)
        self.assertEqual(published['FinalNativeGate-setup-terminal.json']['status'],'COLLECTION_FAILED')

    def test_missing_fixed_source_reports_exact_partial_failure(self):
        status,trace,published=self.collect(missing=True)
        self.assertEqual(status,78)
        self.assertIn('/usr/bin/missing',published['FinalNativeGate-candidate-partial-failure.json']['error'])
        self.assertNotIn('go',trace)

class Bootstrap(unittest.TestCase):
    def test_independent_finite_bootstrap_hash_and_drift(self):
        spec=importlib.util.spec_from_file_location('lifecycle_fixtures',D/'FinalNativeGate-lifecycle-tests.py')
        fixtures=importlib.util.module_from_spec(spec);spec.loader.exec_module(fixtures)
        import FinalNativeGate_bootstrap_seal as seal
        rows={'tiny.py':dict(size=1,sha256=hashlib.sha256(b'x').hexdigest())}
        raw=json.dumps(rows).encode();digest=hashlib.sha256(raw).hexdigest()
        seal_raw=('BOOTSTRAP_SHA256 = '+repr(digest)+'\n').encode()
        tree=fixtures.SyntheticTree({'/':('dir',),'/usr':('dir',),'/usr/bin':('dir',),
            '/usr/bin/tiny.py':('file',b'x'),'/usr/bin/FinalNativeGate-bootstrap.json':('file',raw),
            '/usr/bin/FinalNativeGate_bootstrap_seal.py':('file',seal_raw)})
        class Input(io.BytesIO):
            def __init__(self,path):self.fd=tree.open(str(path),0);super().__init__(tree.nodes[str(path)][1])
            def fileno(self):return self.fd
            def close(self):
                if not self.closed:tree.close(self.fd)
                super().close()
        with tree.patches(),patch.object(Path,'open',lambda path,*a,**kw:Input(path)),patch.object(seal,'BOOTSTRAP_SHA256',digest),patch.object(candidate,'Acquisition',side_effect=AssertionError('candidate bootstrap forbidden')):
            snap=candidate.bootstrap(Path('/usr/bin'))
            self.assertEqual(snap['snapshot']['tiny.py']['pin'],rows['tiny.py'])
            tree.nodes['/usr/bin/tiny.py']=('file',b'y')
            with self.assertRaisesRegex(ValueError,'source hash drift'):candidate.bootstrap(Path('/usr/bin'))
        self.assertFalse(tree.fds)


class CleanupMetadata(unittest.TestCase):
    def test_permission_observation_is_data_not_an_extra_gate(self):
        statrow=NS(st_uid=123,st_gid=456,st_mode=0o100600)
        with patch.dict(observation.adapter.identity,{'self_observation':lambda:{'path':'/mock/FinalNativeGate-pin-setup.scope'}}),patch.object(Path,'read_text',return_value='mock control'),patch.object(observation.os,'open',return_value=99),patch.object(observation.os,'close'),patch.object(observation.os,'stat',return_value=statrow),patch.object(observation.os,'getgroups',return_value=[456]),patch.object(observation.os,'access',return_value=False):
            result=observation.controls()
        self.assertFalse(result['cleanup_control_metadata']['effective_write_access'])
        self.assertIn('UNOBSERVED',result['cleanup_control_metadata']['kernel_write_viability'])

    def test_permission_observation_failure_retained(self):
        with patch.dict(observation.adapter.identity,{'self_observation':lambda:{'path':'/mock/FinalNativeGate-pin-setup.scope'}}),patch.object(Path,'read_text',return_value='mock control'),patch.object(observation.os,'open',side_effect=PermissionError('synthetic')):
            result=observation.controls()
        self.assertEqual(result['cleanup_control_metadata']['kernel_write_viability'],'UNRESOLVED')

if __name__=='__main__':unittest.main(verbosity=2)
