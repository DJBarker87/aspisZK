"""Pure fixture integration only. No real subprocess/native body/host query.
Filesystem/process/control/identity/guard boundaries explicitly mocked.
"""
import ast
import copy
import io
import json
from pathlib import Path
import sys
import types
import unittest
from unittest.mock import patch

D=Path(__file__).resolve().parent
sys.path.insert(0,str(D))
import FinalNativeGate as job
import FinalNativeGate_observe as obs
import FinalNativeGate_adapter as adapter
import FinalNativeGate_policy as loader
G=2**30
# Only four tiny generators from the pinned reviewed fixture; no old regression.
data=loader.load_bundle()
fixture_env={'c':adapter.c,'G':G}
loader.functions(data['fixtures']['source'],['node','fixture','legacy','scope'],fixture_env)


def raw_scope():
    s,_=fixture_env['scope'](high=3*G,cap=4*G)
    for row in s['rows']:
        for name in ('path','parent','owner','domain'):
            if isinstance(row.get(name),str):row[name]=row[name].replace('job.scope','FinalNativeGate-060.scope')
    for k in ('path','unified_path'):
        s['self_observation'][k]=s['self_observation'][k].replace('job.scope','FinalNativeGate-060.scope')
    return s


class MemFile(io.BytesIO):
    def fileno(self):return 12345

class MemPath:
    def __init__(self,store,name=''):self.store=store;self.name=name
    def __truediv__(self,name):return MemPath(self.store,name)
    def open(self,mode):
        if self.name in self.store.records:raise FileExistsError(self.name)
        if self.name==self.store.capture_failure:raise OSError('fixture capture failure')
        self.store.records[self.name]='raw capture opened'
        return MemFile()
    def exists(self):return self.name in self.store.records

class Store:
    def __init__(self):self.records={};self.events=[];self.capture_failure=None
    def save(self,name,value):
        if name in self.records:raise FileExistsError(name)
        self.records[name]=copy.deepcopy(value)
        self.events.append('charge' if 'CHARGED' in name else name)

class FakeGuard:
    error=None
    def start(self):pass
    def check(self):pass
    def remember(self,*a):pass
    def cancel_owned(self):pass
    def finish(self,failed=False):return dict(error=None,lineage='fixture only',failed=failed)

class FakeProc:
    def identity(self,pid):return dict(pid=pid,ppid=42,starttime=124,rss_bytes=100)
    def optional(self,pid):return self.identity(pid)

class Integration(unittest.TestCase):
    def setUp(self):
        self.store=Store();self.s=raw_scope();self.child=types.SimpleNamespace(pid=43,returncode=None)
        self.count=0;self.launch_error=None;self.exit=0
        self.patches=[]
        def use(*a,**kw):
            p=patch(*a,**kw);self.patches.append(p);return p.start()
        self.use=use
        self.addCleanup(lambda:[p.stop() for p in reversed(self.patches)])
        use('FinalNativeGate._modules',return_value=(obs,FakeGuard,lambda:{},lambda *a:None,FakeProc))
        use('FinalNativeGate._plan',return_value={'environment':{},'inherited_limits':{}})
        self.pin={'files':{'source':'fixture'},'native':{'tool':'fixture'},'cache':{}}
        use('FinalNativeGate._pins',side_effect=lambda:copy.deepcopy(self.pin))
        use('FinalNativeGate._pins_after',side_effect=lambda:copy.deepcopy(self.pin))
        use('FinalNativeGate._save',side_effect=self.store.save)
        use('FinalNativeGate_observe.save',side_effect=self.store.save)
        use('FinalNativeGate.PACKET',MemPath(self.store))
        use('FinalNativeGate._packet_check')
        use('os.getpid',return_value=42)
        use('signal.signal')
        use('os.fsync');use('os.close');use('os.pidfd_open',return_value=999,create=True)
        use('signal.pidfd_send_signal',create=True)
        use('time.sleep')
        # No native command can escape. Only exact visibility argv handled.
        use('subprocess.run',side_effect=self.visibility)
        use('subprocess.Popen',side_effect=self.spawn)
        use('os.wait4',side_effect=lambda *a:(43,self.exit<<8,types.SimpleNamespace(ru_maxrss=12,ru_nswap=0)))
        self.patches.append(patch.dict(adapter.identity,scan_bound=lambda:copy.deepcopy(self.s),self_observation=lambda:copy.deepcopy(self.s['self_observation'])))
        self.patches[-1].start()
        self.patches.append(patch.dict(adapter.inventory,inventory=lambda *a:fixture_env['legacy'](self.s,0)['cgroups']))
        self.patches[-1].start()
        use('pathlib.Path.read_text',side_effect=self.read)
    def visibility(self,argv,*a,**kw):
        result={tuple(adapter.COMMANDS[0]):'PID PPID RSS COMMAND CGROUP\n42 1 1 python /fixed\n',
                tuple(adapter.COMMANDS[1]):'',tuple(adapter.COMMANDS[2]):''}
        if tuple(argv) not in result:raise AssertionError('unexpected command '+repr(argv))
        return types.SimpleNamespace(returncode=0,stdout=result[tuple(argv)],stderr='')
    def read(self,*args,**kw):
        # Patched descriptor receives no path through MagicMock; controls raw
        # function below is pinned to a finite fixture receipt instead.
        raise AssertionError('unexpected actual filesystem read')
    def controls(self):
        return dict(path=self.s['self_observation']['path'],pid=42,self_observation=copy.deepcopy(self.s['self_observation']),
          values={k:str(v) for k,v in {'memory.high':3*G,'memory.max':4*G,'memory.swap.max':0,'memory.swap.current':0,'pids.max':64,'memory.peak':G,'memory.current':G,'pids.current':1}.items()}|
          {'memory.events':'high 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0\n'})
    def spawn(self,argv,**kw):
        self.store.events.append('Popen');self.count+=1
        self.assertEqual(argv,list(job.COMMAND));self.assertEqual(kw['env'],{})
        self.assertIn('FinalNativeGate-Kani060-CHARGED.json',self.store.records)
        if self.launch_error:raise self.launch_error
        return self.child
    def execute(self):
        self.use('FinalNativeGate_observe.controls',side_effect=self.controls)
        return job._execute()
    def assert_denied_without_charge(self):
        self.assertEqual(self.execute(),78);self.assertEqual(self.count,0)
        self.assertNotIn('FinalNativeGate-Kani060-CHARGED.json',self.store.records)
    def test_actual_policy_once_counted_and_fixed_spawn(self):
        self.assertEqual(self.execute(),0)
        reports=[v for k,v in self.store.records.items() if k.endswith('-report.json')]
        self.assertEqual(len(reports),2)
        for r in reports:
            self.assertEqual(r['decision']['requested_bytes'],0)
            self.assertEqual(r['decision']['projected_reserved_bytes'],4*G)
        self.assertEqual(self.count,1)
        self.assertLess(self.store.events.index('charge'),self.store.events.index('Popen'))
    def test_old_1g_marker_not_authority(self):
        self.store.records['ResourceMeta1G-epoch7']={'allowed':True}
        self.s['meminfo']['MemAvailable']=1
        self.assert_denied_without_charge()
    def test_wrong_scope(self):
        self.s['self_observation']['path']='/sys/fs/cgroup/wrong.scope'
        self.assert_denied_without_charge()
    def test_wrong_cap(self):
        self.s['rows'][1]['cap']=G
        self.assert_denied_without_charge()
    def test_swap(self):
        self.s['rows'][1]['swap_max']=1
        self.assert_denied_without_charge()
    def test_start_identity(self):
        self.s['self_observation']['starttime']=999
        self.assert_denied_without_charge()
    def test_stale_error(self):
        self.use('subprocess.run',side_effect=OSError('fixture stale visibility error'))
        self.assert_denied_without_charge()
    def test_raw_visibility(self):
        self.use('subprocess.run',return_value=types.SimpleNamespace(returncode=0,stdout='bad header',stderr=''))
        self.assert_denied_without_charge()
    def test_unbounded_populated(self):
        self.s['rows'][1]['cap']=None
        self.assert_denied_without_charge()
    def test_source_tool_environment_policy_failures(self):
        for reason in ['source drift','tool drift','environment drift','policy seal drift']:
            with self.subTest(reason=reason),patch('FinalNativeGate._pins',side_effect=job.Denied(reason)):
                self.assert_denied_without_charge()
                self.store.records.clear();self.store.events.clear()
    def test_pressure(self):
        def pressured():
            c=self.controls();c['values']['memory.events']='high 1\nmax 0\noom 0\noom_kill 0\noom_group_kill 0\n';return c
        self.use('FinalNativeGate_observe.controls',side_effect=pressured)
        self.assertEqual(job._execute(),78);self.assertEqual(self.count,0)
        controls=[v for k,v in self.store.records.items() if k.startswith('FinalNativeGate-control-')]
        self.assertTrue(any('high 1' in c['values']['memory.events'] for c in controls))
    def test_spawn_failure_charged(self):
        self.launch_error=OSError('fixture spawn failed')
        self.assertEqual(self.execute(),78)
        self.assertIn('FinalNativeGate-Kani060-CHARGED.json',self.store.records)
        self.assertEqual(self.count,1)
    def test_capture_failure_no_charge(self):
        self.store.capture_failure='FinalNativeGate-stdout.raw';self.assert_denied_without_charge()
    def test_timeout_charged(self):
        self.exit=124;self.assertEqual(self.execute(),78);self.assertEqual(self.count,1)
        self.assertEqual(self.store.records['FinalNativeGate-terminal.json']['actual_command_exit'],124)
    def test_reap_failure_honest(self):
        self.use('os.wait4',side_effect=ChildProcessError('fixture reap failure'))
        self.assertEqual(self.execute(),78);self.assertEqual(self.count,1)
        terminal=self.store.records['FinalNativeGate-terminal.json']
        self.assertIsNone(terminal['actual_command_exit']);self.assertTrue(terminal['errors'])
    def test_charge_exclusive(self):
        job._charge()
        with self.assertRaises(FileExistsError):job._charge()
        self.assertEqual(self.count,0)

class PinGates(unittest.TestCase):
    def setUp(self):
        self.plan=dict(environment={},inherited_limits={},host_runtime={'runtime':'fixed'},
                       files={'/fixed/source':__import__('hashlib').sha256(b'fixed').hexdigest()},
                       native_roots=['/fixed/native'],native_runtime_dependencies={'native':'hash'},
                       cache_roots=['/fixed/cache'],cache_inventory={},source_revision='fixture')
    def check(self,mutate=None):
        p=copy.deepcopy(self.plan)
        if mutate:mutate(p)
        with patch('FinalNativeGate._plan',return_value=p),patch('FinalNativeGate.HERE',job.STAGE), \
             patch.dict('os.environ',{},clear=True), \
             patch('FinalNativeGate._modules',return_value=(obs,FakeGuard,lambda:{},lambda *a:None,FakeProc)), \
             patch('FinalNativeGate_observe.runtime_pins',return_value={'runtime':'fixed'}), \
             patch('pathlib.Path.read_bytes',return_value=b'fixed'), \
             patch('FinalNativeGate._tree',side_effect=lambda roots:{'native':'hash'} if roots==['/fixed/native'] else {}):
            return job._pins()
    def test_matching_finite_pins(self):
        self.assertEqual(self.check()['files'],self.plan['files'])
    def test_actual_source_gate(self):
        with self.assertRaisesRegex(job.Denied,'source/package/tool'):
            self.check(lambda p:p['files'].update({'/fixed/source':'wrong'}))
    def test_actual_tool_gate(self):
        with self.assertRaisesRegex(job.Denied,'native tool/sysroot'):
            self.check(lambda p:p['native_runtime_dependencies'].update({'native':'wrong'}))
    def test_actual_environment_gate(self):
        with self.assertRaisesRegex(job.Denied,'environment'):
            self.check(lambda p:p['environment'].update({'UNREVIEWED':'1'}))
    def test_actual_runtime_gate(self):
        with self.assertRaisesRegex(job.Denied,'collector runtime'):
            self.check(lambda p:p['host_runtime'].update({'runtime':'wrong'}))
    def test_actual_cache_gate(self):
        with self.assertRaisesRegex(job.Denied,'cache preflight'):
            self.check(lambda p:p['cache_inventory'].update({'extra':'wrong'}))
    def test_actual_rlimit_drift(self):
        from FinalNativeGate_guard import check_limits,GuardError
        good={'RLIMIT_AS':[-1,-1],'RLIMIT_DATA':[-1,-1]}
        with self.assertRaises(GuardError):check_limits(good,good|{'RLIMIT_NOFILE':[1,1]})
    def test_policy_bytes_not_caller_projection(self):
        b=copy.deepcopy(data);b['policy']['source']+='\n# changed\n'
        with self.assertRaisesRegex(ValueError,'immutable source pin drift'):
            loader.validate_bundle(b)
    def test_policy_seal_drift(self):
        with patch('pathlib.Path.read_bytes',return_value=b'{}'):
            with self.assertRaisesRegex(job.Denied,'source seal drift'):job._plan()


class Static(unittest.TestCase):
    def test_both_entries_unconditionally_disabled(self):
        import FinalNativeGate_inside as inside
        for f in (job.main,inside.main):
            with patch('builtins.print'),patch('subprocess.Popen',side_effect=AssertionError('native launch')):
                self.assertEqual(f(),78)
    def test_missing_plan_pins_deny(self):
        with self.assertRaisesRegex(job.Denied,'missing reviewed host'):
            job._plan()
    def test_exact_literal_command(self):
        self.assertEqual(job.COMMAND[0:4],('/usr/bin/timeout','240','/home/dombarker/.cargo/bin/cargo','kani'))
        self.assertEqual(job.COMMAND[job.COMMAND.index('--harness')+1],'checks::paired_coordinate_native_resume')
        self.assertEqual(job.COMMAND[-9:],('-j','1','-Z','unstable-options','-Z','stubbing','--extra-pointer-checks','--cbmc-args','--unwinding-assertions'))

if __name__=='__main__':
    unittest.main(verbosity=2)
