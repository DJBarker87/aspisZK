"""Own offline preflight only; no baseline suite rerun or remote operation."""
import ast
import copy
import importlib.util
import json
from pathlib import Path
import runpy
import sys
import tempfile
import unittest
from unittest.mock import patch
import ResourceActual_host as h

BASE=Path(__file__).resolve().parent.parent/'resource-stat-20261024'
sys.path.insert(0,str(BASE/'baseline'))
from test_go_api import scope_fixture
from test_resource_slab import legacy
api=runpy.run_path(str(BASE/'ResourceStat_go.py'))
g=api['read_only_admission'].__globals__

class Preflight(unittest.TestCase):
    def test_syntax_all_payloads(self):
        for p in Path(__file__).parent.glob('*.py'):
            ast.parse(p.read_text(),filename=str(p))

    def test_scope_argv_controls_and_in_scope_entry(self):
        a=h.scope_argv()
        self.assertEqual(a[:4],['systemd-run','--user','--scope','--unit=resource-actual-20261024'])
        self.assertEqual(a[4:12],['-p','MemoryHigh=3G','-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64'])
        self.assertEqual(a[-1],'go')
        self.assertIn('-I',a)

    def test_prospective_denial_never_creates_scope(self):
        result=h.flow(lambda:{'decision':{'allowed':False,'error':'raw denial'}},lambda:self.fail('scope launched'))
        self.assertFalse(result['scope_created'])
        self.assertEqual(result['prospective_exit'],78)

    def test_go_denial_never_marks(self):
        result=h.go_flow({'decision':{'allowed':False}},lambda:self.fail('marker launched'))
        self.assertIsNone(result['marker_exit'])

    def test_only_go_success_marks(self):
        marked=[]
        self.assertEqual(h.go_flow({'decision':{'allowed':True}},lambda:marked.append(1))['marker_exit'],0)
        self.assertEqual(marked,[1])

    def fixture(self):
        s=scope_fixture()
        s['rows'][-1].update(high=h.EXPECTED['high'],cap=h.EXPECTED['cap'])
        return s

    def test_synthetic_public_api_3_4_count_once(self):
        s=self.fixture()
        with patch.object(g['runpy'],'run_path',return_value={'admission':lambda requested:legacy(s,requested)}),patch.dict(g,scan_bound=lambda:copy.deepcopy(s)):
            report=api['read_only_admission'](phase='inside-scope',additional_bytes=0,expected=h.EXPECTED)
        d=report['decision']
        self.assertTrue(d['allowed'],d)
        self.assertEqual(d['projected_reserved_bytes'],4*2**30)
        self.assertEqual(d['additional_bytes'],0)
        self.assertEqual(d['scope_binding']['observed_limits'],h.EXPECTED)

    def test_actual_proc_identity_not_argument(self):
        # Live identity primitive reads the test process's real procfs on Linux;
        # macOS uses exact synthetic proc bytes and OS PID, not supplied identity.
        pid=h.os.getpid()
        stat=f'{pid} (ResourceActual) '+' '.join(['S']+['0']*18+['123'])
        values={'/proc/self/stat':stat,'/proc/self/status':f'Pid: {pid}\nTgid: {pid}\n','/proc/self/cgroup':'0::/job.scope\n'}
        with patch.object(Path,'read_text',lambda path,*a,**k:values[str(path)]):
            identity=api['self_observation']()
        self.assertEqual(identity['pid'],pid)
        self.assertEqual(identity['path'],'/sys/fs/cgroup/job.scope')
        with self.assertRaises(TypeError):
            api['read_only_admission'](phase='inside-scope',additional_bytes=0,expected=h.EXPECTED,pid=pid)

    def test_public_api_proc_binding_integrated(self):
        s=self.fixture();pid=h.os.getpid()
        row=s['rows'][-1]
        row.update(procs=[pid],threads=[pid],identities=[dict(tid=pid,tgid=pid,starttime=123)])
        s.pop('self_observation')
        stat=f'{pid} (ResourceActual) '+' '.join(['S']+['0']*18+['123'])
        values={'/proc/self/stat':stat,'/proc/self/status':f'Pid: {pid}\nTgid: {pid}\n','/proc/self/cgroup':'0::/job.scope\n'}
        with patch.object(Path,'read_text',lambda path,*a,**k:values[str(path)]),patch.object(g['runpy'],'run_path',return_value={'admission':lambda requested:legacy(s,requested)}),patch.dict(g['base'],scan=lambda:copy.deepcopy(s)):
            report=api['read_only_admission'](phase='inside-scope',additional_bytes=0,expected=h.EXPECTED)
        d=report['decision']
        self.assertTrue(d['allowed'],d)
        self.assertEqual(d['scope_binding']['self_identity']['pid'],pid)
        self.assertEqual(d['projected_reserved_bytes'],4*2**30)

    def test_transport_payloads_offline(self):
        import ResourceActual_local as local
        import subprocess
        def fake(command,**kw):
            # SSH's one remote command is shell quoted; recover Python -c payload.
            import shlex
            argv=shlex.split(command[-1]);ast.parse(argv[-1])
            return subprocess.CompletedProcess(command,0,json.dumps(dict(runtime={},uid=1000,stage_exists=False,parent_uid=1000,parent_mode='0o755',lock_exists=True)),'')
        with tempfile.TemporaryDirectory() as t,patch.object(local,'OUT',Path(t)),patch.object(local.subprocess,'run',fake):
            local.inspect()
            local.stage()
            self.assertEqual(json.loads((Path(t)/'manifest.json').read_text())['env'],local.env(1000))

    def test_missing_or_weaker_control_denies(self):
        for key in h.EXPECTED:
            s=self.fixture();old=legacy(s,0);del s['rows'][-1][key]
            self.assertFalse(api['evaluate'](old,s,s,0,phase='inside-scope',expected=h.EXPECTED)['allowed'])
        s=self.fixture();s['rows'][-1]['cap']=8*2**30
        self.assertFalse(api['evaluate'](legacy(s,0),s,s,0,phase='inside-scope',expected=h.EXPECTED)['allowed'])

    def test_raw_error_retained_by_live_api(self):
        s=self.fixture()
        def fail():
            e=PermissionError(13,'memory.max unreadable')
            e.read_attempts=[dict(path='/sys/fs/cgroup/job.scope/memory.max',errno=13,error='raw error')]
            raise e
        with patch.object(g['runpy'],'run_path',return_value={'admission':lambda requested:legacy(s,requested)}),patch.dict(g,scan_bound=fail):
            report=api['read_only_admission'](phase='inside-scope',additional_bytes=0,expected=h.EXPECTED)
        self.assertFalse(report['decision']['allowed'])
        self.assertEqual(report['decision']['collection_failures']['before']['read_attempts'][0]['error'],'raw error')

    def test_pin_drift_and_missing_pin_deny(self):
        with tempfile.TemporaryDirectory() as t,patch.object(h,'HERE',Path(t)):
            p=Path(t)/'source.py';p.write_text('old')
            pins={'files':{'source.py':h.filepin(p)},'runtime':{},'env':{}}
            p.write_text('new')
            with self.assertRaisesRegex(ValueError,'source drift'):h.verify(pins)
            p.unlink()
            with self.assertRaises(FileNotFoundError):h.verify(pins)

    def test_runtime_and_environment_drift_deny(self):
        pins={'files':{},'runtime':{'old':1},'env':{}}
        with patch.object(h,'runtime_pins',return_value={'new':1}):
            with self.assertRaisesRegex(ValueError,'runtime/dependency drift'):h.verify(pins)
        pins['runtime']={}
        with patch.object(h,'runtime_pins',return_value={}):
            with self.assertRaisesRegex(ValueError,'environment'):h.verify(pins)

if __name__=='__main__':unittest.main(verbosity=2)
