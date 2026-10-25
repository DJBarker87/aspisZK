"""One focused pure/mock suite. No backend/native/process/security API executes."""
import ast
import copy
import hashlib
import json
import os
from pathlib import Path
import sys
import types
import unittest
from unittest.mock import patch, Mock
import SbfProducer_continue as flow
import SbfProducer_observe as obs
import SbfProducer_package as pkg
import SbfProducer_process as proc
from SbfProducerLinux_capture import Denied

HERE = Path(__file__).parent
G = 2**30


def synthetic():
    """Use reviewed raw fixture construction, not a supplied policy result."""
    bundle = json.loads((HERE/'SbfProducerRss_reviewed.json').read_text())
    source = bundle['fixtures']['source']
    tree = ast.parse(source)
    nodes = [n for n in tree.body if isinstance(n,ast.FunctionDef) and
             n.name in ('node','fixture','legacy','scope')]
    env = dict(c=obs.adapter.c, G=G)
    exec(compile(ast.Module(body=nodes,type_ignores=[]), 'reviewed-raw-fixtures','exec'),env)
    snapshot, expected = env['scope'](high=3*G,cap=4*G)
    row = snapshot['rows'][-1]
    old = row['path']
    row['path'] = row['domain'] = '/sys/fs/cgroup/'+pkg.UNIT+'.scope'
    snapshot['self_observation'].update(path=row['path'], unified_path='/'+pkg.UNIT+'.scope')
    return snapshot, expected, env['legacy']


class Suite(unittest.TestCase):
    def test_exact_copy_and_operational_functions(self):
        mapping = json.loads((HERE.parents[1]/'evidence/sbf-producer-20261025/SbfProducer-identity.json').read_text())
        for name, record in mapping['files'].items():
            raw = (HERE/name).read_bytes()
            self.assertEqual(hashlib.sha256(raw).hexdigest(), record['copied_sha256'])
            for old,new in reversed(mapping['renames']):
                raw = raw.replace(new.encode(),old.encode())
            self.assertEqual(pkg.digest(raw), {k:record[k] for k in ('sha256','size')})
        original = ast.parse((HERE/'SbfProducerRss_host.py').read_text())
        changed = ast.parse((HERE/'SbfProducer_observe.py').read_text())
        for name in ('collect','controls','check_controls','runtime_pins'):
            a = next(n for n in original.body if isinstance(n,ast.FunctionDef) and n.name==name)
            b = next(n for n in changed.body if isinstance(n,ast.FunctionDef) and n.name==name)
            self.assertEqual(ast.dump(a),ast.dump(b))
        original=ast.parse((HERE/'SbfProducerLinux_backend.py').read_text())
        candidate=ast.parse((HERE/'SbfProducer_backend_candidate.py').read_text())
        changed={'guest','internal_backend'}
        for a in original.body:
            if isinstance(a,ast.FunctionDef) and a.name not in changed:
                b=next(n for n in candidate.body if isinstance(n,ast.FunctionDef) and n.name==a.name)
                self.assertEqual(ast.dump(a),ast.dump(b))

    def test_policy_full_raw_count_once_and_deductions(self):
        s,expected,legacy = synthetic()
        d = obs.adapter.policy.evaluate(legacy(s,0),s,copy.deepcopy(s),0,
            phase='inside-scope',expected=expected,expected_unit=pkg.UNIT+'.scope')
        self.assertTrue(d['allowed'],d)
        self.assertEqual(d['projected_reserved_bytes'],4*G)
        self.assertEqual(d['required_bytes'],11*G)
        self.assertEqual(d['safe_limit_bytes'],55*G)
        self.assertEqual(d['adjusted_available_bytes'],74*G)
        for field in ('Active(file)','KReclaimable','SReclaimable'):
            b = copy.deepcopy(s);b['meminfo'][field] += (-2 if field=='SReclaimable' else 1)*G
            result = obs.adapter.policy.evaluate(legacy(b,0),b,b,0,phase='inside-scope',expected=expected,expected_unit=pkg.UNIT+'.scope')
            self.assertEqual(result['adjusted_available_bytes'],73*G)

    def test_actual_adapter_recomputes_twice_and_never_accepts_go(self):
        s,expected,legacy = synthetic()
        policy = obs.adapter.policy.evaluate
        with patch.object(obs.adapter,'visibility',return_value=legacy(s,0)), \
             patch.dict(obs.adapter.identity,scan_bound=Mock(side_effect=[s,copy.deepcopy(s)])), \
             patch.object(obs.adapter.policy,'evaluate',wraps=policy) as evaluate, \
             patch.object(obs.adapter.os,'getpid',return_value=42):
            report = obs.adapter.read_only_admission(phase='inside-scope')
            self.assertTrue(report['decision']['allowed'],report)
            self.assertEqual(obs.adapter.identity['scan_bound'].call_count,2)
            evaluate.assert_called_once()
        with patch.object(obs.adapter,'visibility',side_effect=OSError('visibility denied')), \
             patch.dict(obs.adapter.identity,scan_bound=Mock(return_value=s)):
            self.assertFalse(obs.adapter.read_only_admission(phase='inside-scope')['decision']['allowed'])

    def test_policy_wrong_unit_controls_start_raw_and_1g_deny(self):
        for mutation in ('unit','1g','tasks','swap','start','raw','population','thread','pressure'):
            s,expected,legacy = synthetic();old = legacy(s,0);b=copy.deepcopy(s)
            if mutation=='unit':unit='old-marker.scope'
            else:unit=pkg.UNIT+'.scope'
            r=b['rows'][-1]
            if mutation=='1g':r['cap']=G;r['high']=G
            if mutation=='tasks':r['tasks_max']=65
            if mutation=='swap':r['swap_max']=1
            if mutation=='start':b['self_observation']['starttime']+=1
            if mutation=='raw':b['rows']=[]
            if mutation=='population':r['populated']=False
            if mutation=='thread':r['threads']=[999]
            if mutation=='pressure':b['meminfo']['MemAvailable']=G
            d=obs.adapter.policy.evaluate(old,s,b,0,phase='inside-scope',expected=expected,expected_unit=unit)
            self.assertFalse(d['allowed'],(mutation,d))

    def test_root_order_no_backend_on_any_guard_failure(self):
        approved = dict(runtime={'files':[]})
        events=[]
        before=[dict(pid=42)]
        backend=Mock(side_effect=lambda: events.append('backend') or 0)
        candidate=types.ModuleType('SbfProducer_backend_candidate')
        candidate.validate_runtime=lambda _: events.append('runtime')
        candidate.producer_fixed_body=backend
        with patch.dict(sys.modules,SbfProducer_backend_candidate=candidate), \
             patch.object(flow.os,'getresuid',return_value=(0,0,0),create=True), \
             patch.object(flow.os,'getresgid',return_value=(0,0,0),create=True), \
             patch.object(flow,'approval',return_value=approved), \
             patch.object(flow.proc,'lineage',side_effect=lambda _:events.append('lineage') or before), \
             patch.object(flow,'fresh',side_effect=lambda *_:events.append('full fresh')), \
             patch.object(flow,'pins',return_value={'process':before[-1]}):
            self.assertEqual(flow.root_continuation(),0)
            self.assertEqual(events,['lineage','full fresh','lineage','runtime','lineage','backend'])
            backend.reset_mock()
            for failed in ('source','env','map','scope','controls','pressure','limited','projection','old1g'):
                with patch.object(flow,'fresh',side_effect=Denied(failed)):
                    with self.assertRaises(Denied):flow.root_continuation()
                backend.assert_not_called()
            with patch.object(flow.proc,'lineage',side_effect=[before,[dict(pid=43)]]):
                with self.assertRaises(Denied):flow.root_continuation()
            backend.assert_not_called()

    def test_fresh_executes_collector_and_rechecks_pins(self):
        s,expected,legacy=synthetic()
        approved=dict(scope_path='/'+pkg.UNIT+'.scope')
        ident=s['self_observation']
        controls=dict(self_observation=dict(ident,reads={}))
        with patch.object(flow,'pins',return_value={'same':'pins'}), \
             patch.object(obs,'controls',return_value=controls), \
             patch.object(obs,'check_controls',return_value=True), \
             patch.object(obs,'save') as save, patch.object(flow,'journal'), \
             patch.object(obs.adapter,'visibility',return_value=legacy(s,0)), \
             patch.dict(obs.adapter.identity,scan_bound=Mock(return_value=s)), \
             patch.object(flow.os,'getpid',return_value=42), \
             patch.object(obs.subprocess,'run',side_effect=AssertionError('no live command')):
            self.assertEqual(flow.fresh(approved,'helper'),{'same':'pins'})
            self.assertEqual(obs.adapter.identity['scan_bound'].call_count,2)
            self.assertIn('inside-scope-report.json',[c.args[0] for c in save.call_args_list])
            with patch.object(flow,'pins',side_effect=[{'old':1},{'new':1}]):
                with self.assertRaises(Denied):flow.fresh(approved,'helper')

    def test_exact_controls_pressure_errors(self):
        values={'memory.high':str(3*G),'memory.max':str(4*G),'memory.swap.max':'0',
                'memory.swap.current':'0','pids.max':'64','memory.peak':'42',
                'memory.current':'42','pids.current':'2',
                'memory.events':'high 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0\n'}
        self.assertTrue(obs.check_controls({'values':values}))
        for key in values:
            b=dict(values);b[key]={'error':'read denied'}
            with self.assertRaises((ValueError,TypeError)):obs.check_controls({'values':b})
        b=dict(values);b['memory.events']=values['memory.events'].replace('high 0','high 1')
        with self.assertRaises(ValueError):obs.check_controls({'values':b})

    def test_package_alias_writer_staging_and_cleanup(self):
        from types import SimpleNamespace as NS
        base=dict(st_mode=0o100444,st_uid=0,st_gid=0,st_nlink=1,st_size=1,
                  st_dev=1,st_ino=2,st_mtime_ns=1,st_ctime_ns=1)
        for change in ({},{'st_nlink':2},{'st_uid':1000},{'st_mode':0o100644}):
            api=Mock();api.open.return_value=11;api.fstat.return_value=NS(**dict(base,**change))
            api.read.side_effect=[b'x',b'']
            if change:
                with self.assertRaises(Denied):pkg.pinned_file('/opt/fixed',pkg.digest(b'x'),0o444,api,lambda _:10)
            else:self.assertEqual(pkg.pinned_file('/opt/fixed',pkg.digest(b'x'),0o444,api,lambda _:10),b'x')
            self.assertEqual([c.args[0] for c in api.close.call_args_list],[11,10])
        with self.assertRaises(Denied):pkg.approval()

    def test_disabled_entry_and_lifecycle_source(self):
        for name in ('SbfProducer_entry.py','SbfProducer_user_entry.py'):
            tree=ast.parse((HERE/name).read_text())
            self.assertEqual([type(n).__name__ for n in tree.body],['Expr','Raise'])
        s=(HERE/'SbfProducer_backend_candidate.py').read_text()
        self.assertLess(s.index('abi.drop(last_cap)'),s.index("abi.prctl(1,9) == 0, 'guest parent-death rearm'"))
        self.assertLess(s.index('parent_alive(3)'),s.index('dropped_check(ns,cgroup'))
        self.assertNotIn('os.kill(',s)
        self.assertIn('internal_backend(root,output,nullfd,abi,manifest=manifest)',s)
        self.assertIn('source contains submounts',s)
        self.assertIn('api.close(selfpidfd)',s)

    def test_actual_pins_env_limits_source_and_runtime(self):
        approved=dict(env=pkg.ENV,limits={'helper':{'fake':'limits'}},
                      host={'helper':{'full':'runtime'}},scope_path='/'+pkg.UNIT+'.scope',
                      roles={'helper':{'expected':'proc'}})
        row=dict(cgroup='0::'+approved['scope_path']+'\n')
        with patch.object(flow,'verify_package',return_value={'fixed':'source'}), \
             patch.dict(flow.os.environ,pkg.ENV,clear=True), \
             patch.object(flow,'inherited_limits',return_value={'fake':'limits'}), \
             patch.object(flow,'check_limits') as limits, \
             patch.object(obs,'runtime_pins',return_value={'full':'runtime'}), \
             patch.object(flow.proc,'process',return_value=row) as process:
            result=flow.pins(approved,'helper')
            self.assertEqual(result['package'],{'fixed':'source'})
            limits.assert_called_once_with({'fake':'limits'},{'fake':'limits'})
            process.assert_called_once_with(os.getpid(),'helper',{'expected':'proc'})
            with patch.dict(flow.os.environ,{'UNAPPROVED':'x'}):
                with self.assertRaises(Denied):flow.pins(approved,'helper')
            with patch.object(obs,'runtime_pins',return_value={'limited':'map'}):
                with self.assertRaises(Denied):flow.pins(approved,'helper')
            with patch.object(flow,'verify_package',side_effect=Denied('old source')):
                with self.assertRaises(Denied):flow.pins(approved,'helper')

    def test_concrete_live_ancestry_optional_monitor_and_reparent(self):
        for monitor in (False,True):
            roles={r:{'exe':r} for r in ('collector','sudo','sudo-monitor','helper')}
            approved=dict(roles=roles,scope_path='/'+pkg.UNIT+'.scope')
            cg='0::'+approved['scope_path']+'\n'
            ids={'collector':40,'sudo':41,'sudo-monitor':42,'helper':43}
            chain=['collector','sudo']+(['sudo-monitor'] if monitor else [])+['helper']
            rows={ids[role]:dict(pid=ids[role],ppid=ids[chain[i-1]] if i else 1,
                      starttime=100+ids[role],role=role,cgroup=cg)
                  for i,role in enumerate(chain)}
            def observed(pid,role,expected):
                self.assertEqual(rows[pid]['role'],role)
                return rows[pid]
            with patch.object(proc.os,'getpid',return_value=43), \
                 patch.object(proc,'stat',side_effect=lambda pid:rows[pid]), \
                 patch.object(proc,'executable',return_value='sudo' if monitor else 'collector'), \
                 patch.object(proc,'process',side_effect=observed):
                self.assertEqual([r['role'] for r in proc.lineage(approved)],chain)
                rows[43]['cgroup']='0::/old.scope\n'
                with self.assertRaises(Denied):proc.lineage(approved)

    def test_live_process_reads_bind_all_metadata_and_start(self):
        status=('Tgid: 43\nPid: 43\nThreads: 1\nUid: 0 0 0 0\nGid: 0 0 0 0\n'
                'Groups: \nCapInh: 0\nCapPrm: ff\nCapEff: ff\nCapBnd: ff\nCapAmb: 0\n'
                'NoNewPrivs: 0\nSeccomp: 0\n').encode()
        cg='0::/'+pkg.UNIT+'.scope\n'
        data={'/proc/43/status':status,'/proc/43/environ':b'A=B\0',
              '/proc/43/cmdline':b'fixed\0','/proc/43/cgroup':cg.encode(),
              '/proc/43/maps':b'1-2 r-xp 0 00:00 1 /opt/fixed\n2-3 r-xp 0 00:00 0 [vdso]\n',
              '/proc/43/limits':b'actual inherited limits'}
        expected=dict(exe={'hash':'exe'},uid=[0]*4,gid=[0]*4,groups=[],
            caps={'Inh':0,'Prm':255,'Eff':255,'Bnd':255,'Amb':0},threads=1,nnp=0,seccomp=0,
            env=pkg.digest(b'A=B\0'),cmdline=pkg.digest(b'fixed\0'),
            limits=pkg.digest(b'actual inherited limits'),
            maps={'/opt/fixed':{'pin':{'sha256':'p','size':1},'mode':0o555}},
            kernel_maps=[['[vdso]','r-xp']])
        stable=dict(pid=43,ppid=42,starttime=9)
        with patch.object(proc,'read',side_effect=lambda path,*_:data[path]), \
             patch.object(proc,'stat',return_value=stable), \
             patch.object(proc,'executable',return_value={'hash':'exe'}), \
             patch.object(proc,'pinned_file') as pinned:
            self.assertEqual(proc.process(43,'helper',expected)['starttime'],9)
            pinned.assert_called_once_with('/opt/fixed',{'sha256':'p','size':1},0o555)
            for key in ('env','limits','exe','uid','kernel_maps'):
                bad=dict(expected);bad[key]='old'
                with self.assertRaises(Denied):proc.process(43,'helper',bad)
            with patch.object(proc,'stat',side_effect=[stable,dict(stable,starttime=10)]):
                with self.assertRaises(Denied):proc.process(43,'helper',expected)
            data['/proc/43/maps']=b'1-2 rwxp 0 00:00 0\n'
            with self.assertRaises(Denied):proc.process(43,'helper',expected)

    def test_backend_owned_child_gate_cleanup_mock_only(self):
        import SbfProducer_backend_candidate as backend
        for failure in ('pidfd','signal0','gate','wait','success'):
            api=Mock();abi=Mock();output=Mock();events=[]
            api.pipe2.return_value=(20,21);api.fork.return_value=88
            api.getpid.return_value=43;api.write.return_value=1
            api.waitpid.return_value=(88,0)
            abi.call.side_effect=[30,31] if failure!='pidfd' else [30,OSError('pidfd')]
            if failure=='signal0':abi.check_owned_signal.side_effect=OSError('LSM SIG0')
            if failure=='gate':api.write.return_value=0
            with patch.object(backend,'root_helper_preflight',return_value=({},b'cg',40)), \
                 patch.object(backend,'pidfd_identity'), \
                 patch.object(backend,'owned_wait',side_effect=Denied('wait') if failure=='wait' else None,
                              return_value=(88,0)):
                if failure=='success':
                    self.assertIs(backend.internal_backend(10,output,11,abi,api=api),output.collect.return_value)
                    output.collect.assert_called_once_with(88,88,0)
                else:
                    with self.assertRaises((OSError,Denied)):
                        backend.internal_backend(10,output,11,abi,api=api)
                    output.collect.assert_not_called()
                    api.waitpid.assert_called_once_with(88,0)
                    if failure!='pidfd':abi.kill_owned.assert_called_once_with(31)
                self.assertIn(30,[c.args[0] for c in api.close.call_args_list])
                self.assertIn(21,[c.args[0] for c in api.close.call_args_list])
                api.fork.assert_called_once()


if __name__ == '__main__':
    unittest.main()
