"""Synthetic only: no host, systemd, reservation or consumer."""
import copy
from pathlib import Path
import unittest
from unittest.mock import patch
import go_api as go
from test_resource_slab import fixture, node, legacy

EXPECTED = dict(high=6*go.GIB, cap=8*go.GIB, swap_max=0, tasks_max=64)


def scope_fixture(ancestor=False):
    path='/sys/fs/cgroup/job.scope'
    row=node(path,go.GIB,cap=8*go.GIB,owner='/sys/fs/cgroup')
    s=fixture(row)
    s['rows'][0].update(path='/sys/fs/cgroup',owner='/sys/fs/cgroup',domain='/sys/fs/cgroup',subtree_pids=True)
    row.update(high=6*go.GIB,procs=[42],threads=[42],pids_enabled=True,
               tasks_max=64,pids_current=1,identities=[dict(tid=42,tgid=42,starttime=123)])
    if ancestor:
        parent=node('/sys/fs/cgroup/parent',go.GIB,cap=12*go.GIB,subtree=True,owner='/sys/fs/cgroup')
        parent.update(subtree_pids=True,pids_enabled=True,tasks_max=128,pids_current=1,high=10*go.GIB)
        row.update(path=parent['path']+'/job.scope',parent=parent['path'],owner=parent['path'],domain=parent['path']+'/job.scope')
        s['rows'].insert(1,parent)
    s['self_observation']=dict(pid=42,starttime=123,path=row['path'],unified_path=row['path'][len('/sys/fs/cgroup'):])
    return s


class GoTests(unittest.TestCase):
    def decision(self,s,**kwargs):
        return go.evaluate(legacy(s,0),s,copy.deepcopy(s),0,phase='inside-scope',expected=EXPECTED,**kwargs)

    def test_go_counts_own_scope_once(self):
        s=scope_fixture();d=self.decision(s)
        self.assertTrue(d['allowed'],d)
        self.assertEqual(d['additional_bytes'],0)
        self.assertEqual(d['projected_reserved_bytes'],8*go.GIB)
        self.assertEqual(d['scope_binding']['finite_frontier_association'],s['rows'][-1]['path'])

    def test_covering_ancestor_counted_once(self):
        s=scope_fixture(True);d=self.decision(s)
        self.assertTrue(d['allowed'],d)
        self.assertEqual(d['projected_reserved_bytes'],12*go.GIB)
        self.assertEqual(d['scope_binding']['finite_frontier_association'],s['rows'][1]['path'])

    def test_prospective_positive_cap_remains_additional(self):
        s=scope_fixture();d=go.evaluate(legacy(s,4*go.GIB),s,s,4*go.GIB,phase='prospective')
        self.assertTrue(d['allowed']);self.assertEqual(d['projected_reserved_bytes'],12*go.GIB)

    def test_phase_and_additional_contract(self):
        s=scope_fixture()
        for phase,q in [('unknown',0),('prospective',0),('inside-scope',1)]:
            self.assertFalse(go.evaluate(legacy(s,q),s,s,q,phase=phase,expected=EXPECTED if phase=='inside-scope' else None)['allowed'])
        self.assertFalse(go.evaluate(legacy(s,1),s,s,1,phase='prospective',expected=EXPECTED)['allowed'])

    def test_wrong_or_missing_actual_controls(self):
        for key,value in [('high',5*go.GIB),('cap',7*go.GIB),('swap_max',None),('tasks_max',65),('swap_current',1)]:
            s=scope_fixture();s['rows'][-1][key]=value
            self.assertFalse(self.decision(s)['allowed'],key)
        for key in EXPECTED:
            s=scope_fixture();old=legacy(s,0);del s['rows'][-1][key]
            self.assertFalse(go.evaluate(old,s,s,0,phase='inside-scope',expected=EXPECTED)['allowed'],key)

    def test_missing_pid_or_identity_or_memory_disabled(self):
        for key,value in [('procs',[]),('identities',[]),('enabled',False),('populated',False),('pids_enabled',False)]:
            s=scope_fixture();old=legacy(s,0);s['rows'][-1][key]=value
            self.assertFalse(go.evaluate(old,s,s,0,phase='inside-scope',expected=EXPECTED)['allowed'])

    def test_ancestor_high_and_max_below_expected_deny(self):
        for key,value in [('cap',7*go.GIB),('high',5*go.GIB),('tasks_max',63)]:
            s=scope_fixture(True);s['rows'][1][key]=value
            self.assertFalse(self.decision(s)['allowed'])

    def test_fake_path_outside_scope_missing_self_and_self_race(self):
        s=scope_fixture();s['self_observation']['path']='/sys/fs/cgroup/fake.scope'
        self.assertFalse(self.decision(s)['allowed'])
        s=scope_fixture();s['self_observation']['unified_path']='/outside'
        self.assertFalse(self.decision(s)['allowed'])
        s=scope_fixture();del s['self_observation']
        self.assertFalse(self.decision(s)['allowed'])
        s=scope_fixture();after=copy.deepcopy(s);after['self_observation']['starttime']=124
        self.assertFalse(go.evaluate(legacy(s,0),s,after,0,phase='inside-scope',expected=EXPECTED)['allowed'])

    def test_expected_controls_are_required_and_not_unknown(self):
        s=scope_fixture()
        for expected in (None,{},dict(EXPECTED,cap=0),dict(EXPECTED,swap_max=1),dict(EXPECTED,tasks_max=63),dict(EXPECTED,extra=1)):
            self.assertFalse(go.evaluate(legacy(s,0),s,s,0,phase='inside-scope',expected=expected)['allowed'])

    def test_legacy_visibility_physical_cap_and_available_denials_remain(self):
        s=scope_fixture();old=legacy(s,0);old['visibility_error']='unknown'
        self.assertFalse(go.evaluate(old,s,s,0,phase='inside-scope',expected=EXPECTED)['allowed'])
        s['meminfo']['MemAvailable']=2*go.GIB
        self.assertFalse(self.decision(s)['allowed'])
        s=scope_fixture();s['meminfo'].update(MemTotal=16*go.GIB,MemFree=14*go.GIB,MemAvailable=10*go.GIB)
        self.assertFalse(self.decision(s)['allowed'])
        s=scope_fixture(True);s['rows'][1]['cap']=go.LIMIT
        self.assertFalse(self.decision(s)['allowed'])


class LiveBindingTests(unittest.TestCase):
    def observation(self, mutate=None):
        stat='42 (self name) '+' '.join(['S']+['0']*18+['123'])
        data={'/proc/self/stat':stat,'/proc/self/status':'Pid: 42\nTgid: 42\n','/proc/self/cgroup':'0::/job.scope\n'}
        if mutate: data.update(mutate)
        def read(path,*a,**kw):
            value=data[str(path)]
            if isinstance(value,Exception):raise value
            return value
        with patch.object(Path,'read_text',read),patch.object(go.os,'getpid',return_value=42):
            return go.self_observation()

    def test_proc_self_derived_not_supplied(self):
        obs=self.observation()
        self.assertEqual(obs['path'],'/sys/fs/cgroup/job.scope')
        self.assertEqual(len(obs['reads']),4)
        self.assertRaises(TypeError,go.scan_bound,path='/fake.scope')

    def test_unreadable_missing_and_noncanonical_self_deny(self):
        for path in ('/proc/self/stat','/proc/self/status','/proc/self/cgroup'):
            self.assertRaises(OSError,self.observation,{path:PermissionError(13,'unreadable')})
        for groups in ('','0::/../fake.scope','0::/job.scope\n0::/fake.scope','0::/x//fake.scope'):
            self.assertRaises(ValueError,self.observation,{'/proc/self/cgroup':groups})
        self.assertRaises(ValueError,self.observation,{'/proc/self/status':'Pid: 43\nTgid: 42'})

    def test_live_self_migration_denies(self):
        obs=self.observation();changed=dict(obs,unified_path='/other.scope',path='/sys/fs/cgroup/other.scope')
        with patch.object(go,'self_observation',side_effect=[obs,changed]),patch.dict(go.base,scan=lambda:scope_fixture()):
            self.assertRaises(ValueError,go.scan_bound)

    def test_actual_outside_scope_not_admitted(self):
        s=scope_fixture();row=s['rows'][-1]
        row.update(path='/sys/fs/cgroup/session.service',domain='/sys/fs/cgroup/session.service')
        s['self_observation'].update(path=row['path'],unified_path='/session.service')
        self.assertFalse(self.decision(s)['allowed'])

    decision=GoTests.decision

class PublicAdapterTests(unittest.TestCase):
    def test_public_live_adapter_has_no_scope_or_pid_override(self):
        self.assertRaises(TypeError,go.read_only_admission,phase='inside-scope',additional_bytes=0,expected=EXPECTED,path='/fake.scope')
        s=scope_fixture()
        with patch.object(go.runpy,'run_path',return_value={'admission':lambda requested:legacy(s,requested)}),patch.object(go,'scan_bound',side_effect=[s,copy.deepcopy(s)]):
            report=go.read_only_admission(phase='inside-scope',additional_bytes=0,expected=EXPECTED)
        self.assertTrue(report['decision']['allowed'])
        self.assertEqual(report['decision']['projected_reserved_bytes'],8*go.GIB)

    def test_live_adapter_unreadable_control_denies(self):
        s=scope_fixture()
        with patch.object(go.runpy,'run_path',return_value={'admission':lambda requested:legacy(s,requested)}),patch.object(go,'scan_bound',side_effect=PermissionError(13,'memory.max unreadable')):
            report=go.read_only_admission(phase='inside-scope',additional_bytes=0,expected=EXPECTED)
        self.assertFalse(report['decision']['allowed'])
        self.assertEqual(set(report['decision']['collection_failures']),{'before','after'})

class GoCollectorTests(unittest.TestCase):
    def test_remote_payload_and_receipt_without_host(self):
        import ast
        import importlib.util
        import json
        import subprocess
        from tempfile import TemporaryDirectory
        spec=importlib.util.spec_from_file_location('go_collector',Path(__file__).with_name('collect_go_readonly.py'))
        collector=importlib.util.module_from_spec(spec);spec.loader.exec_module(collector)
        report=dict(legacy_read_inputs=[],snapshots=dict(before=None,after=None),decisions={},original_legacy={},failures={},collection_error='synthetic missing snapshot')
        def transport(command,*,input,**kw):
            ast.parse(input)
            self.assertIn("candidate=virtual_run('go_api.py')",input)
            return subprocess.CompletedProcess(command,0,json.dumps(report),'')
        with TemporaryDirectory() as temp,patch.object(collector,'OUT',Path(temp)),patch.object(collector.subprocess,'run',transport),patch.object(collector.subprocess,'check_output',return_value='synthetic'):
            collector.main()
            receipt=json.loads((Path(temp)/'live-command.json').read_text())
            self.assertEqual(receipt['api_version'],go.API_VERSION)
            self.assertEqual(receipt['exit'],0)
