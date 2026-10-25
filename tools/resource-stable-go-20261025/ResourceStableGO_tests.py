"""Focused new integration groups only. No live transport or historical suite."""
import ast
import copy
import contextlib
import io
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import ResourceStableGO_adapter as a
import ResourceStableGO_host as h
import ResourceStableGO_local as local
import ResourceStableGO_sources as sources
import ResourceStableGO_audit as audit
from ResourceStableGO_fixtures import fixture, kernel, virtual

class ResourceStableGOTests(unittest.TestCase):
    def test_staged_loader_hard_pins_transparent_aliases(self):
        data=sources.bundle()
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/'ResourceStableGO_reviewed.json';p.write_text(json.dumps(data))
            with patch.object(sources,'HERE',Path(t)),patch.object(sources,'bundle',side_effect=AssertionError('staged Git forbidden')):
                c,go,identity,inventory,policy=sources.load()
                self.assertIs(policy.observe,c.observe);self.assertIs(policy.bind_scope,go['bind_scope'])
                self.assertIn('self_observation',identity);self.assertIn('inventory',inventory)
                self.assertRaises(RuntimeError,policy.read_only_admission,phase='prospective',additional_bytes=1)
                self.assertRaises(RuntimeError,go['read_only_admission'],phase='prospective',additional_bytes=1)
                bad=copy.deepcopy(data);bad['policy']['source']+='\n# drift\n'
                bad['policy'].update(sources.digest(bad['policy']['source'].encode()))
                p.write_text(json.dumps(bad))
                with self.assertRaisesRegex(ValueError,'pin drift'):sources.load()
                bad=copy.deepcopy(data);del bad['identity'];p.write_text(json.dumps(bad))
                with self.assertRaisesRegex(ValueError,'set drift'):sources.load()
        tree=ast.parse(Path(a.__file__).read_text())
        calls=[ast.unparse(n.func) for n in ast.walk(tree) if isinstance(n,ast.Call)]
        self.assertEqual(calls.count('policy.evaluate'),1)
        self.assertNotIn("go['evaluate']",calls)

    def test_real_proc_adapter_expected_unit_collector_race(self):
        for phase in ('prospective','inside-scope'):
            for ancestor in (False,True):
                with kernel(fixture(ancestor)):report=a.read_only_admission(phase=phase)
                self.assertTrue(report['decision']['allowed'],report['decision'].get('error'))
                self.assertEqual(report['decision']['additional_bytes'],4*a.c.GIB if phase=='prospective' else 0)
                self.assertEqual(report['decision']['collector_identity']['pid'],os.getpid())
        s=fixture();original=s['rows'][-1]['path'];replacement=original.replace(a.UNIT,'other')
        s['rows'][-1].update(path=replacement,domain=replacement)
        s['self_observation'].update(path=replacement,unified_path=replacement[len('/sys/fs/cgroup'):])
        with kernel(s):self.assertFalse(a.read_only_admission(phase='inside-scope')['decision']['allowed'])
        with kernel(fixture()) as files:
            files['/proc/self/stat']='1 (fake) '+' '.join(['S']+['0']*18+['123'])+'\n'
            self.assertFalse(a.read_only_admission(phase='prospective')['decision']['allowed'])
        for key in ('pid','path'):
            with self.assertRaises(TypeError):a.read_only_admission(phase='inside-scope',**{key:'fake'})

    def test_changed_policy_unrelated_delta_only_and_fail_closed(self):
        # Complete real scan_bound calls over two independently valid virtual
        # kernels. No evaluator or scanner global is replaced.
        s=fixture();pid=s['self_observation']['pid'];r=s['rows'][-1]
        r['threads'].append(pid+100);r['identities'].append(dict(tid=pid+100,tgid=pid,starttime=9));r['pids_current']=2
        later=fixture()
        first=virtual(s);second=virtual(later);self_reads=0
        def read(path,*args,**kw):
            nonlocal self_reads
            # scan_bound reads /proc/self/stat four times per full snapshot.
            if str(path)=='/proc/self/stat':self_reads+=1
            return (first if self_reads<=4 else second)[1](path,*args,**kw)
        with patch.object(Path,'read_text',read),patch.object(os,'scandir',first[2]),patch.object(subprocess,'run',first[3]):
            report=a.read_only_admission(phase='prospective')
        self.assertTrue(report['decision']['allowed'],report['decision'].get('error'))
        self.assertTrue(report['decision']['membership_differences'])
        # Real scanner internal loss and read/visibility failure stay gating.
        for key in ('/proc/self/status',f'/proc/{pid}/status',r['path']+'/pids.current'):
            with kernel(fixture()) as files:
                files[key]=PermissionError(13,'focused synthetic denied')
                self.assertFalse(a.read_only_admission(phase='prospective')['decision']['allowed'])
        with kernel(fixture()),patch.object(subprocess,'run',side_effect=subprocess.CalledProcessError(1,a.COMMANDS[0])):
            self.assertFalse(a.read_only_admission(phase='prospective')['decision']['allowed'])
        with kernel(fixture()) as files:
            files[r['path']+'/pids.current']='2\n'
            self.assertFalse(a.read_only_admission(phase='prospective')['decision']['allowed'])

    def test_literal_inner_env_clears_dirty_strict_check(self):
        expected=local.env(1000);argv=h.scope_argv(dict(env=expected))
        self.assertEqual(argv[:14],['/usr/bin/systemd-run','--user','--scope','--unit='+h.UNIT,'-p','MemoryHigh=3G','-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/env','-i'])
        self.assertEqual(argv[21:],['/usr/bin/python3','-I','-B',h.STAGE+'/ResourceStableGO_host.py','go'])
        dirty=dict(expected,INVOCATION_ID='dirty',JOURNAL_STREAM='dirty',SYSTEMD_EXEC_PID='dirty',LANG='dirty')
        result=subprocess.run(argv[12:21]+['/usr/bin/env'],env=dirty,check=True,capture_output=True,text=True)
        observed=dict(line.split('=',1) for line in result.stdout.splitlines())
        self.assertEqual(observed,expected)
        with patch.dict(os.environ,observed,clear=True):h.verify_environment(expected)
        for bad in (dirty,dict(expected,UNKNOWN='private-dirty-value'),dict(expected,LANG='drift'),{k:v for k,v in expected.items() if k!='HOME'}):
            with patch.dict(os.environ,bad,clear=True),self.assertRaises(ValueError) as error:h.verify_environment(expected)
            self.assertNotIn('private-dirty-value',str(error.exception))
        self.assertEqual(shlex.split(shlex.join(argv)),argv)

    def test_denied_scope_marker_once_transport_error_and_coordination(self):
        denied=dict(decision=dict(allowed=False))
        self.assertFalse(h.flow(lambda:denied,lambda:self.fail('scope'))['scope_created'])
        self.assertIsNone(h.go_flow(denied,lambda:self.fail('marker'))['marker_exit'])
        with tempfile.TemporaryDirectory() as t,patch.object(local,'OUT',Path(t)),patch.object(local,'coordination',return_value={}),patch.object(local,'revision',return_value='synthetic'):
            root=Path(t);(root/'manifest.json').write_text(json.dumps(dict(env=local.env(1000))))
            local.charge()
            with self.assertRaises(FileExistsError):local.charge()
            with patch.object(subprocess,'run',side_effect=subprocess.TimeoutExpired(['ssh'],120,output=b'kept failure')):
                with self.assertRaises(subprocess.TimeoutExpired):local.run()
            self.assertTrue((root/'RUN_ATTEMPTED').exists());self.assertTrue((root/'run-transport.json').exists())
            with self.assertRaises(FileExistsError):local.run()
        with patch.object(subprocess,'run',return_value=subprocess.CompletedProcess([],0,'18006 active','')),patch.object(Path,'read_bytes',side_effect=AssertionError('live output forbidden')):
            with self.assertRaisesRegex(RuntimeError,'WAITING'):local.coordination()

    def test_epoch_source_argv_runtime_drift_and_control_gates(self):
        with tempfile.TemporaryDirectory() as t,patch.object(h,'HERE',Path(t)),patch.object(h,'STAGE',t):
            p=Path(t)/'x';p.write_text('old')
            m=dict(epoch=h.EPOCH,stage=t,env=local.env(1000),mode=h.MODE,files={'x':h.filepin(p)},runtime={})
            m['scope_argv']=h.scope_argv(m)
            with self.assertRaisesRegex(ValueError,'literal scope argv'):h.verify(dict(m,scope_argv=[]))
            p.write_text('new')
            with self.assertRaisesRegex(ValueError,'source drift'):h.verify(m)
            p.write_text('old')
            with patch.object(h,'runtime_pins',return_value={'drift':1}),self.assertRaisesRegex(ValueError,'runtime/dependency'):h.verify(m)
        values={'memory.high':str(h.EXPECTED['high']),'memory.max':str(h.EXPECTED['cap']),'memory.swap.max':'0','memory.swap.current':'0','pids.max':'64','pids.current':'1','memory.current':'100','memory.peak':'200','memory.events':'low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0\n'}
        self.assertTrue(h.check_controls(dict(values=values)))
        for name,value in [('memory.swap.current','1'),('memory.peak',str(5*a.c.GIB)),('pids.max','65'),('memory.events',values['memory.events'].replace('high 0','high 1'))]:
            with self.assertRaises(ValueError):h.check_controls(dict(values=dict(values,**{name:value})))

    def test_new_ordered_replay_pass_denial_and_tamper(self):
        for phase,fault in (('prospective',False),('inside-scope',False),('prospective',True)):
            with tempfile.TemporaryDirectory() as t,patch.object(h,'HERE',Path(t)):
                with kernel(fixture()) as files:
                    if fault:files['/proc/self/status']=PermissionError(13,'new synthetic failure')
                    report=h.collect(phase)
                self.assertEqual(report['decision']['allowed'],not fault)
                cap=Path(t)/'capture';pins={p.name:dict(name=p.name,**h.filepin(p)) for p in cap.iterdir()}
                (cap/'export-receipt.json').write_text(json.dumps(dict(host_files=pins)))
                with patch.object(audit,'OUT',cap):self.assertEqual(audit.replay(phase)['allowed'],not fault)
                p=cap/(phase+'-ordered.json');events=json.loads(p.read_text());events[0]['path']='/tampered';p.write_text(json.dumps(events))
                with patch.object(audit,'OUT',cap),self.assertRaises(AssertionError):audit.replay(phase)

    def test_source_seals_and_staging_payload(self):
        for p in Path(__file__).parent.glob('ResourceStableGO_*.py'):ast.parse(p.read_text())
        def transport(payload,label,environment=None,data=None):
            ast.parse(payload)
            self.assertEqual(label,'stage');x=json.loads(data)
            with tempfile.TemporaryDirectory() as t:
                stage=Path(t).resolve()/'stage';x['manifest']['parent_resolved']=str(stage.parent)
                code=payload.replace(repr(local.REMOTE),repr(str(stage)))
                with patch.object(__import__('sys'),'stdin',io.StringIO(json.dumps(x))),contextlib.redirect_stdout(io.StringIO()):exec(code,{})
                self.assertEqual(stage.stat().st_mode & 0o777,0o700)
                with patch.object(sources,'HERE',stage),patch.object(sources,'bundle',side_effect=AssertionError('no staged git')):
                    self.assertEqual(sources.load()[4].API_VERSION,'ResourceStability20261025-v1')
            return subprocess.CompletedProcess([],0,'{}','')
        with tempfile.TemporaryDirectory() as t,patch.object(local,'OUT',Path(t)),patch.object(local,'ssh_python',transport):
            (Path(t)/'runtime-inspection.json').write_text(json.dumps(dict(runtime={},uid=os.getuid(),parent_resolved='/unused')))
            local.stage()

if __name__=='__main__':unittest.main(verbosity=2)
