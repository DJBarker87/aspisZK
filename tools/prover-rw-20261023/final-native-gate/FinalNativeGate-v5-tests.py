"""v5 focused source fixtures: OS/host boundaries mocked; private temp files only."""
import contextlib
import copy
import importlib.util
import json
import os
from pathlib import Path
import stat
import subprocess
import tempfile
from types import SimpleNamespace as NS
import unittest
from unittest.mock import Mock,patch,mock_open
import FinalNativeGate_setup as setup
import FinalNativeGate_setup_observe as observe
import FinalNativeGate_compact as compact
import FinalNativeGate_cleanup as cleanup
import FinalNativeGate_scope as scopes
import FinalNativeGate_guard as guards
import FinalNativeGate_candidate as candidate
from FinalNativeGate_policy import load,load_bundle
observation=observe
guard_module=guards
scope=scopes
D=Path(__file__).resolve().parent


def module(name):
    spec=importlib.util.spec_from_file_location(name,D/(name+'.py'))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


class Compact(unittest.TestCase):
    def test_large_raw_known_shape_not_traversed_or_serialized(self):
        class Raw(dict):
            def items(self):raise AssertionError('raw traversed')
            def __iter__(self):raise AssertionError('raw traversed')
        raw=Raw(payload='RAW_SECRET'*((14*2**20)//10))
        report=dict(decision=dict(allowed=False,error='exact bounded cause',cap_ok=False,
            available_ok=True,legacy_nonreserve_gate_ok=True,margin_bytes=-123,
            legacy=raw,before_observation=raw,after_observation=raw,
            collection_failures={'before':dict(error='denied',type='PermissionError',errno=13,raw_inputs=raw,read_attempts=raw)}),
            snapshots=raw,original_legacy=raw)
        with patch.object(compact.json,'dumps',wraps=json.dumps) as dumps:
            record=compact.project('prospective',report)
        self.assertLess(len(json.dumps(record)),65536)
        self.assertNotIn('RAW_SECRET',json.dumps(record));self.assertNotIn('raw_inputs',json.dumps(record))
        self.assertEqual(record['decision']['error'],'exact bounded cause');self.assertEqual(record['decision']['margin_bytes'],-123)
        for call in dumps.call_args_list:self.assertIsNot(call.args[0],report)
        self.assertEqual(record['allowed'],False);self.assertFalse(record['reporting_failed'])

    def test_unknown_error_bounds_and_no_success_defaults(self):
        for value in (None,{},dict(decision={}),dict(decision={'allowed':1})):
            r=compact.project('go',value);self.assertIsNone(r['allowed']);self.assertTrue(r['reporting_failed'])
        r=compact.project('go',dict(decision=dict(allowed=True,error='inconsistent')))
        self.assertTrue(r['reporting_failed'])
        r=compact.project('go',dict(decision=dict(allowed=False,error='x'*70000)))
        self.assertTrue(r['reporting_failed']);self.assertEqual(r['decision']['error']['size'],70000)
        self.assertLess(len(json.dumps(r)),65536)
        # Combined bound:16 reasons times6 escaped bytes per character.
        r=compact.project('go',dict(decision=dict(allowed=False,reasons=['\x00'*2048]*16)))
        self.assertEqual(r['status'],'reporting_error');self.assertIn('sha256',r);self.assertNotIn('decision',r)

    def test_real_policy_no_change_and_inside_go_history(self):
        c,go,identity,inventory,policy=load()
        bundle=load_bundle();ns={}
        # Pinned synthetic fixture definitions only; no historical run/cache.
        import sys,types
        alias=types.ModuleType('ResourceAvailable_candidate');alias.__dict__.update(c.__dict__)
        go_alias=types.ModuleType('ResourceAvailable_go');go_alias.__dict__.update(go)
        with patch.dict(sys.modules,ResourceAvailable_candidate=alias,ResourceAvailable_go=go_alias):
            exec(bundle['fixtures']['source'],ns)
        for phase in ('prospective','inside-scope','go'):
            if phase=='prospective':snapshot,_=ns['scope']();expected=None;requested=2**30;unit=None
            else:
                snapshot,expected=ns['scope'](768*2**20,2**30)
                unit=Path(snapshot['self_observation']['path']).name;requested=0
            old=ns['legacy'](snapshot,requested)
            decision=policy.evaluate(old,snapshot,snapshot,requested,phase='inside-scope' if phase=='go' else phase,expected=expected,expected_unit=unit)
            self.assertTrue(decision['allowed'],decision)
            report=dict(decision=decision);before=copy.deepcopy(report)
            r=compact.project(phase,report)
            self.assertEqual(report,before);self.assertTrue(r['allowed']);self.assertFalse(r['reporting_failed'])
            for k in compact.NUMBERS:
                if k in decision:self.assertEqual(r['decision'][k],decision[k])
            self.assertEqual(r['phase'],phase)
            self.assertNotIn('before_observation',r['decision'])

    def test_collect_history_before_raw_publication_fault_and_private_save(self):
        history=[]
        with patch.object(observe.adapter,'read_only_admission',return_value={'decision':{'allowed':False,'error':'new cause'}}),patch.object(observe,'save',side_effect=OSError('disk fault')):
            with self.assertRaises(OSError):observe.collect('prospective',admission=history)
        self.assertEqual(history[0]['decision']['error'],'new cause')
        packet=Path(tempfile.mkdtemp(prefix='FinalNativeGate-v5-private-',dir='/private/tmp'))
        with patch.object(setup,'PACKET',packet):
            previous=os.umask(0o002)
            try:
                with patch.object(observe.adapter,'read_only_admission',return_value={'decision':{'allowed':False,'error':'new cause'}}):
                    history=[];report=observe.collect('prospective',admission=history)
            finally:os.umask(previous)
        for entry in packet.iterdir():self.assertEqual(stat.S_IMODE(entry.stat().st_mode),0o600)
        self.assertEqual(history[0]['full_evidence'],report['raw_receipts']);self.assertEqual(len(list(packet.iterdir())),3)


class Lifecycle(unittest.TestCase):
    def test_verified_no_start_and_owned_or_uncertain_paths(self):
        for state,child,fd,binding in (('not_started',None,None,None),('uncertain',None,None,None),
                                    ('not_started',NS(returncode=0),None,None),('not_started',None,99,{})):
            scope=Mock(fd=fd,binding=binding);scope.finish.return_value={'unresolved':False}
            guard=Mock();guard.finish.return_value={}
            r=cleanup.cleanup(child,None,None,guard,Mock(),scope,outer=True,spawn_state=state)
            guard.cancel_owned.assert_called_once();guard.finish.assert_called_once();guard.check.assert_called_once()
            if state=='not_started' and child is None and fd is None:
                scope.cancel_owned.assert_not_called();scope.finish.assert_not_called()
                self.assertEqual(r['scope']['status'],'not_started');self.assertIsNone(r['scope_cancel_outcome'])
            else:scope.cancel_owned.assert_called_once();scope.finish.assert_called_once()
        scope=scopes.FixedScope('setup');guard=Mock();guard.finish.return_value={}
        r=cleanup.cleanup(None,None,None,guard,Mock(),scope,outer=True,spawn_state='uncertain')
        self.assertTrue(r['unresolved']);self.assertEqual(len(r['errors']),3)

    def parent(self,*,denied=True,uncertain=False,publish_fault=None):
        import fcntl
        published={};guard=Mock();guard.finish.return_value={};scope=scopes.FixedScope('setup')
        scope.preflight=Mock();scope.bind_release=Mock();scope.cancel_owned=Mock(side_effect=ValueError('ownership unbound'));scope.finish=Mock(side_effect=ValueError('ownership unbound'))
        def collect(phase,admission):
            r=dict(decision=dict(allowed=not denied,error='exact new denial') if denied else dict(allowed=True))
            admission.append(compact.project(phase,r));return r
        def publish(name,value):
            if name==publish_fault:raise OSError('write fault')
            published[name]=copy.deepcopy(value)
        child=NS(pid=4242,returncode=None)
        with contextlib.ExitStack() as stack:
            bindings=[(setup,'HERE',setup.STAGE),(setup,'_inputs',lambda:{}),(setup,'_guard',lambda:guard),(setup,'_publish',publish),
                (setup.signal,'signal',Mock()),(Path,'mkdir',Mock()),(Path,'open',mock_open()),
                (scopes,'FixedScope',lambda kind:scope),(scopes,'environment',lambda:{}),(observe,'collect',collect),
                (candidate,'bootstrap',lambda stage:{}),(candidate,'stable',Mock()),(guards,'Proc',lambda:Mock()),
                (subprocess,'Popen',Mock(side_effect=OSError('uncertain spawn') if uncertain else AssertionError('spawn forbidden'))),(fcntl,'flock',Mock())]
            for obj,key,value in bindings:stack.enter_context(patch.object(obj,key,value))
            stack.enter_context(patch('builtins.open',mock_open()))
            code=setup._prospective()
        return code,published,scope

    def test_denial_before_spawn_parent_compact_and_no_owned_control(self):
        code,published,scope=self.parent()
        self.assertEqual(code,78);scope.preflight.assert_not_called();scope.cancel_owned.assert_not_called();scope.finish.assert_not_called()
        r=published['FinalNativeGate-setup-parent-terminal.json']
        self.assertTrue(r['failed']);self.assertFalse(r['unresolved']);self.assertEqual(r['spawn_state'],'not_started')
        self.assertEqual(r['admission'][0]['decision']['error'],'exact new denial')
        self.assertEqual(published['FinalNativeGate-setup-parent-cleanup.json']['scope']['status'],'not_started')

    def test_uncertain_spawn_retains_unresolved_and_control_errors(self):
        code,published,scope=self.parent(denied=False,uncertain=True)
        self.assertEqual(code,78);scope.cancel_owned.assert_called_once();scope.finish.assert_called_once()
        self.assertTrue(published['FinalNativeGate-setup-parent-terminal.json']['unresolved'])

    def test_denial_prior_write_fault_terminal_truth(self):
        code,published,_=self.parent(publish_fault='FinalNativeGate-setup-parent-guard.json')
        self.assertEqual(code,78);self.assertTrue(published['FinalNativeGate-setup-parent-terminal.json']['failed'])
        self.assertIn('write fault',str(published['FinalNativeGate-setup-parent-terminal.json']['errors']))


class V5Order(unittest.TestCase):
    def collect(self,deny=None,control_error=False,missing=False):
        trace=[];published={};phase=None
        def mark(name,value=None):
            trace.append(name);return value
        def admission(value,admission):
            nonlocal phase
            phase=value
            report={'decision':{'allowed':value!=deny}}
            admission.append(compact.project(value,report))
            return mark(value,report)
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
        terminal=published['FinalNativeGate-setup-terminal.json']
        self.assertFalse(terminal['execution_authority']);self.assertFalse(terminal['failed'])
        self.assertEqual([r['phase'] for r in terminal['admission']],['inside-scope','go'])
        self.assertTrue(all(r['allowed'] for r in terminal['admission']))

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


class V5Release(unittest.TestCase):
    def test_exact_new_root_and_mismatch_refusal(self):
        old=module('FinalNativeGate-v4-tests');old.R=D/'prospective-data-v5'
        ns=old.receiver();self.assertEqual(ns['STAGE'],'/home/dombarker/final-native-gate-v5-20261025')
        tree=old.Tree(ns);ns['os']=tree.api;ns['STAGE']='/home/dombarker/other'
        with self.assertRaisesRegex(ValueError,'leaf mismatch'):ns['install']()
        self.assertFalse(tree.fds)

    def test_exact_nonstage_plan_and_nulls_preserved(self):
        old=module('FinalNativeGate-v4-tests');old.R=D/'prospective-data-v5';ns=old.receiver()
        rows=ns['decoded']();p=json.loads(rows['FinalNativeGate-plan.json'])
        # Immutable beforeimage copied by local runner; no historical live source.
        before=json.loads((D.parents[2]/'evidence/prover-rw-20261023/final-native-gate/v5-beforeimages-019/FinalNativeGate-plan.json').read_bytes())
        def external(files,stage):return {k:v for k,v in files.items() if not k.startswith(stage+'/')}
        self.assertEqual(external(p['files'],ns['STAGE']),external(before['files'],'/home/dombarker/final-native-gate'))
        for k in before:
            if k not in ('files','job_source_sizes','job_revision','setup_catalog_roots'):self.assertEqual(p[k],before[k],k)
        self.assertEqual(sum(v is None for v in before.values()),7)
        self.assertEqual(set(p['setup_catalog_roots']),set(p['native_roots'])|set(p['files']))


def suite(release=False):
    result=unittest.TestSuite()
    for cls in (Compact,Lifecycle,V5Order) if not release else (V5Release,):result.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(cls))
    if not release:
        publication=module('FinalNativeGate-receipt-publication-tests')
        result.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(publication.Publication))
    if release:
        old=module('FinalNativeGate-v4-tests');old.R=D/'prospective-data-v5'
        result.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(old.Release))
        for name in ('test_fresh_0775_ancestor_denied_and_secure_0750_accepted','test_preexisting_directory_regular_and_dangling_alias_denied','test_exact_coverage_and_manifest_tamper_denied'):
            result.addTest(old.PathRepair(name))
    return result

if __name__=='__main__':
    import sys
    result=unittest.TextTestRunner(verbosity=2).run(suite('--release' in sys.argv))
    raise SystemExit(not result.wasSuccessful())
