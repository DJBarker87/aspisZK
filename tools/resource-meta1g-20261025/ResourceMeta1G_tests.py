"""Focused source-only metadata delta checks. All operational callers use TEMP/stubs."""
import ast
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import ResourceMeta1G_adapter as adapter
import ResourceMeta1G_guard as guard
import ResourceMeta1G_host as host
import ResourceMeta1G_local as local
import ResourceMeta1G_sources as sources

OUT=local.OUT

def normalized(raw, record, renames):
    text=raw.decode()
    for old,new in reversed(record['semantic_replacements']):
        assert text.count(new)==1, (record['path'],new)
        text=text.replace(new,old)
    for old,new in reversed(renames):text=text.replace(new,old)
    return text.encode()

def fixtures():
    # Load only four pure fixture helpers from the pinned reviewed test source.
    env=dict(c=adapter.c,G=adapter.c.GIB)
    return sources.functions(sources.bundle()['fixtures']['source'],['node','fixture','legacy','scope'],env)

F=fixtures(); G=adapter.c.GIB

def snapshot(high=768*2**20,cap=G):
    s,e=F['scope'](high,cap)
    row=s['rows'][-1]; old=row['path'];new=old.rsplit('/',1)[0]+'/'+host.UNIT+'.scope'
    row.update(path=new,domain=new,current=min(cap,128*2**20))
    s['self_observation'].update(path=new,unified_path='/'+host.UNIT+'.scope')
    return s,e

def evaluate(s,expected=None,q=0,phase='inside-scope'):
    return adapter.policy.evaluate(F['legacy'](s,q),s,s,q,phase=phase,
        expected=expected,expected_unit=host.UNIT+'.scope' if phase=='inside-scope' else None)

def controls(high=768*2**20,cap=G):
    values={'memory.high':str(high),'memory.max':str(cap),'memory.swap.max':'0',
        'memory.swap.current':'0','pids.max':'64','memory.peak':'1000','memory.current':'1000',
        'pids.current':'2','memory.events':'high 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0\n'}
    return dict(values=values)

def wire():
    return dict(limit_platform=dict(platform='linux',rlim_infinity=-1),
        inherited_limits=dict(RLIMIT_AS=[-1,-1],RLIMIT_DATA=[-1,-1],RLIMIT_CPU=[-1,-1]))

class ResourceMeta1GTests(unittest.TestCase):
    def setUp(self):self.original_limits=guard.inherited_limits()
    def tearDown(self):self.assertEqual(guard.inherited_limits(),self.original_limits)

    def test_normalized_bytes_ast_finite_deltas_and_policy_pins(self):
        identity=json.loads((OUT/'ResourceMeta1G-identity.json').read_text())
        for name,record in identity['files'].items():
            before=subprocess.check_output(['git','show',record['revision']+':'+record['path']],cwd=local.ROOT)
            after=(local.HERE/name).read_bytes()
            self.assertEqual(host.digest(before),record['before']);self.assertEqual(host.digest(after),record['after'])
            normal=normalized(after,record,identity['renames'])
            self.assertEqual(normal,before)
            self.assertEqual(ast.dump(ast.parse(normal),include_attributes=True),ast.dump(ast.parse(before),include_attributes=True))
        sources.validate_bundle(sources.bundle())
        self.assertEqual(guard.BUDGET,512*2**20)
        # Source inventory has no setter, old auditor, native or backend entry.
        for p in local.HERE.glob('*.py'):
            if p.name.endswith('_tests.py'):continue
            tree=ast.parse(p.read_text())
            self.assertFalse(any(isinstance(n,ast.Attribute) and n.attr=='setrlimit' for n in ast.walk(tree)))

    def test_all_metadata_paths_and_own_charge_once_other_jobs_retained(self):
        self.assertEqual(adapter.EXPECTED,host.EXPECTED)
        self.assertEqual(host.EXPECTED,dict(high=768*2**20,cap=G,swap_max=0,tasks_max=64))
        argv=host.scope_argv(dict(env=local.env(1000)))
        for value in ('MemoryHigh=768M','MemoryMax=1G','MemorySwapMax=0','TasksMax=64','--unit='+host.UNIT):
            self.assertEqual(argv.count(value),1)
        self.assertNotIn('--replace',argv)
        s,e=snapshot(); other=F['node']('/sys/fs/cgroup/other.scope',current=G,cap=8*G,owner='/sys/fs/cgroup')
        other.update(pids_enabled=True,pids_current=0,tasks_max=64)
        s['rows'].append(other); untouched=copy.deepcopy(other)
        d=evaluate(s,e);self.assertTrue(d['allowed'],d)
        self.assertEqual(d['additional_bytes'],0);self.assertEqual(d['projected_reserved_bytes'],9*G)
        self.assertEqual(d['scope_binding']['observed_limits'],host.EXPECTED)
        self.assertEqual(other,untouched)
        self.assertEqual(d['required_consumer_scope'],dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,stricter_existing='5G/7G unchanged'))
        with patch.object(adapter,'visibility',side_effect=lambda q:F['legacy'](s,q)) as visibility,patch.dict(adapter.identity,scan_bound=lambda:copy.deepcopy(s)):
            prospective=adapter.read_only_admission(phase='prospective')
            visibility.assert_called_once_with(G)
            self.assertEqual(prospective['decision']['additional_bytes'],G)
            self.assertEqual(prospective['decision']['projected_reserved_bytes'],10*G)
            self.assertTrue(prospective['decision']['allowed'])
            inside=adapter.read_only_admission(phase='inside-scope')
            self.assertTrue(inside['decision']['allowed']);self.assertEqual(inside['decision']['projected_reserved_bytes'],9*G)
        self.assertTrue(host.check_controls(controls()))

    def test_historical_and_mismatched_controls_cannot_authorize(self):
        for high,cap in ((3*G,4*G),(768*2**20,4*G),(3*G,G),(6*G,8*G)):
            s,_=snapshot(high,cap)
            self.assertFalse(evaluate(s,host.EXPECTED)['allowed'])
            with self.assertRaises(ValueError):host.check_controls(controls(high,cap))
        s,_=snapshot()
        for high,cap in ((3*G,4*G),(6*G,8*G),(5*G,7*G)):
            expected=dict(high=high,cap=cap,swap_max=0,tasks_max=64)
            self.assertFalse(evaluate(s,expected)['allowed'])
            with self.assertRaises(ValueError):adapter.go['bind_scope'](s,expected)
        with self.assertRaises(RuntimeError):adapter.go['read_only_admission'](phase='prospective',additional_bytes=G)
        with self.assertRaises(RuntimeError):adapter.policy.read_only_admission(phase='prospective',additional_bytes=G)

    def test_retained_actual_report_is_historical_denial_not_authority(self):
        raw=subprocess.check_output(['git','show','45d137dd34:evidence/resource-rss-go-v3-20261025/EVIDENCE-offline-replay.json'],cwd=local.ROOT)
        report=json.loads(raw)
        self.assertFalse(report['phases']['inside-scope']['allowed'])
        self.assertEqual(report['phases']['inside-scope']['margin_bytes'],-552960)
        self.assertEqual(report['go_exit']['terminal'],'GO_DENY')
        for values in report['controls'].values():
            observed=controls();observed['values'].update(values)
            with self.assertRaisesRegex(ValueError,'scope control drift'):host.check_controls(observed)
        # No evaluation, numerical projection, ordered reads or collector replay here.

    def test_wire_wholemap_strict_linux_and_bootstrap_temp(self):
        good=wire();local.check_remote_linux_limits(good,good['inherited_limits'])
        for platform,infinity in (('darwin',-1),('linux',True),('linux',-1.0),('linux',0)):
            bad=copy.deepcopy(good);bad['limit_platform']=dict(platform=platform,rlim_infinity=infinity)
            with self.assertRaises(guard.GuardError):local.check_remote_linux_limits(bad)
        for name in ('RLIMIT_AS','RLIMIT_DATA'):
            for value in (0,4096,True,-1.0,-2):
                bad=copy.deepcopy(good);bad['inherited_limits'][name][0]=value
                with self.assertRaises(guard.GuardError):local.check_remote_linux_limits(bad)
        for mutate in ('extra','missing','changed'):
            expected=copy.deepcopy(good['inherited_limits'])
            if mutate=='extra':expected['RLIMIT_FUTURE']=[-1,-1]
            if mutate=='missing':del expected['RLIMIT_CPU']
            if mutate=='changed':expected['RLIMIT_CPU']=[1,1]
            with self.assertRaises(guard.GuardError):local.check_remote_linux_limits(good,expected)
        with tempfile.TemporaryDirectory(prefix='ResourceMeta1G-wire-') as tmp:
            with patch.object(local,'REMOTE',str(Path(tmp).resolve()/'unused-stage')):
                tree=ast.parse(local.inspection_payload())
            # Execute actual bootstrap top level with only runtime/limits providers stubbed.
            for n in tree.body:
                if isinstance(n,ast.FunctionDef) and n.name in ('runtime_pins','inherited_limits'):
                    value={} if n.name=='runtime_pins' else good['inherited_limits']
                    n.body=ast.parse('return '+repr(value)).body
            output=io.StringIO()
            with patch.object(sys,'platform','linux'),patch.object(resource,'RLIM_INFINITY',-1),contextlib.redirect_stdout(output):
                exec(compile(ast.fix_missing_locations(tree),'ResourceMeta1G-TEMP-bootstrap','exec'),{})
            observed=json.loads(output.getvalue());local.check_remote_linux_limits(observed,good['inherited_limits'])
            self.assertFalse(observed['stage_exists']);self.assertEqual(list(Path(tmp).iterdir()),[])

    def test_actual_inspect_and_stage_temp_only_charge_terminal(self):
        for mode in ('success','wrong-wire','transport-exit','transport-error'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory(prefix='ResourceMeta1G-inspect-') as tmp:
                root=Path(tmp).resolve();out=root/'out';out.mkdir();remote=root/'new-stage';calls=[]
                info=dict(wire(),uid=os.getuid(),parent_uid=os.getuid(),parent_resolved=str(root),runtime={},stage_exists=False)
                if mode=='wrong-wire':info['limit_platform']['rlim_infinity']=True
                def transport(payload,label,environment=None,data=None):
                    self.assertTrue((out/'ATTEMPTED').exists());calls.append(label)
                    if label=='inspect':
                        if mode=='transport-error':raise OSError('stub transport failure')
                        return SimpleNamespace(returncode=1 if mode=='transport-exit' else 0,stdout=json.dumps(info))
                    self.assertEqual(label,'stage')
                    # Real stage bootstrap, ONLY within this test's temporary tree.
                    with patch.object(sys,'stdin',io.StringIO(data)),contextlib.redirect_stdout(io.StringIO()):
                        exec(compile(payload,'ResourceMeta1G-TEMP-stage','exec'),{})
                    return SimpleNamespace(returncode=0)
                with patch.object(local,'OUT',out),patch.object(local,'REMOTE',str(remote)),patch.object(local,'ssh_python',transport):
                    if mode=='success':
                        local.inspect()
                        with patch.object(local,'sources',return_value={'ResourceMeta1G_stub.py':'# TEMP only\n'}):local.stage()
                        self.assertTrue((remote/'ResourceMeta1G_manifest.json').exists())
                    else:
                        with self.assertRaises((RuntimeError,OSError)):local.inspect()
                        if mode=='wrong-wire':
                            with patch.object(local,'sources',side_effect=AssertionError('packaging reached')):
                                with self.assertRaises(guard.GuardError):local.stage()
                    with self.assertRaises(FileExistsError):local.inspect()
                self.assertEqual(calls,['inspect','stage'] if mode=='success' else ['inspect'])

    def test_terminal_reserve_denial_sourcepin_unit_collision(self):
        marker=[];launch=[]
        s,e=snapshot();s['meminfo']['MemAvailable']=8*G
        denied=evaluate(s,e);self.assertFalse(denied['allowed'])
        self.assertEqual(host.go_flow(dict(decision=denied),lambda:marker.append(True))['terminal'],'GO_DENY')
        self.assertEqual(host.flow(lambda:dict(decision=denied),lambda:launch.append(True))['terminal'],'PROSPECTIVE_DENY')
        self.assertEqual(marker+launch,[])
        bad=sources.bundle();bad['policy']['source']+='\n# changed\n'
        with self.assertRaisesRegex(ValueError,'pin drift'):sources.load(bad)
        with tempfile.TemporaryDirectory(prefix='ResourceMeta1G-sourcepin-') as tmp:
            root=Path(tmp);p=root/'ResourceMeta1G_host.py';p.write_text('# drift\n')
            manifest=dict(epoch=host.EPOCH,stage=host.STAGE,mode=host.MODE,env=local.env(1000),files={p.name:host.digest(b'# original\n')})
            manifest['scope_argv']=host.scope_argv(manifest)
            with patch.object(host,'HERE',root),patch.object(host,'STAGE',str(root)),patch.object(host,'runtime_pins',side_effect=AssertionError('runtime reached')):
                manifest.update(stage=str(root));manifest['scope_argv']=host.scope_argv(manifest)
                with self.assertRaisesRegex(ValueError,'source drift'):host.verify(manifest)
        with tempfile.TemporaryDirectory(prefix='ResourceMeta1G-collision-') as tmp:
            root=Path(tmp);(root/'ResourceMeta1G_manifest.json').write_text('{}');lock=root/'lock';lock.touch();calls=[]
            def collision(argv,stdout,stderr,**kw):
                calls.append(argv);stderr.write('Failed to start transient scope unit: Unit already exists.\n');stdout.close();stderr.close()
                return SimpleNamespace(pid=12345,returncode=None)
            with patch.object(host,'HERE',root),patch.object(host,'LOCK',str(lock)),patch.object(host,'ACTIVE_GUARD',SimpleNamespace(check=lambda:None)),patch.object(host,'verify',return_value={}),patch.object(host,'collect',return_value=dict(decision=dict(allowed=True))),patch.object(host,'scope_argv',return_value=host.scope_argv(dict(env=local.env(1000)))),patch.object(host.subprocess,'Popen',side_effect=collision),patch.object(host.os,'wait4',return_value=(12345,256,SimpleNamespace(ru_maxrss=1,ru_nswap=0))),patch.object(sys,'argv',['ResourceMeta1G_host.py','run']):
                # main only needs the env when launching the stubbed child.
                (root/'ResourceMeta1G_manifest.json').write_text(json.dumps(dict(env=local.env(1000))))
                self.assertEqual(host.main(),78)
                with self.assertRaises(FileExistsError):host.main()
            self.assertEqual(len(calls),1);self.assertFalse((root/'capture/marker.json').exists())
            self.assertEqual(json.loads((root/'capture/scope-child.json').read_text())['exit'],1)
            # scope_created=True is inherited attempt reporting, not proof of creation.

    def test_no_real_operational_artifacts(self):
        for name in ('ATTEMPTED','RUN_ATTEMPTED','runtime-inspection.json','manifest.json','marker.json'):
            self.assertFalse((OUT/name).exists(),name)
        self.assertFalse(Path(host.STAGE).exists())

def seal():
    dependencies={}
    for name,module in sorted(sys.modules.items()):
        path=getattr(module,'__file__',None)
        if path and Path(path).is_file() and Path(path).suffix in ('.py','.so'):
            dependencies[name]=dict(path=path,**host.filepin(path))
    historical={}
    for name in ('ResourceRssGOv3-focused-corrected-receipt.json','ResourceRssGOv3-SOURCE-ASSESSMENT.md','EVIDENCE-offline-receipt.json','EVIDENCE-offline-replay.json'):
        path='evidence/resource-rss-go-v3-20261025/'+name
        raw=subprocess.check_output(['git','show','45d137dd34:'+path],cwd=local.ROOT)
        historical[path]=dict(revision='45d137dd34',**host.digest(raw),assessment='REUSED historical evidence; not a new source/identity/admission gate')
    reviewed=sources.bundle();sources.validate_bundle(reviewed)
    value=dict(status='SOURCE_ONLY; no actual admission or marker',source_revision=local.revision(),
        dependencies=dependencies,sources={p.name:host.filepin(p) for p in sorted(local.HERE.glob('*.py'))},
        reviewed_dependencies={k:{n:v[n] for n in ('revision','path','sha256','size')} for k,v in reviewed.items()},
        identity_manifest=host.filepin(OUT/'ResourceMeta1G-identity.json'),historical_references=historical,
        host_operations=0,epoch='UNUSED identifier; six previous epochs charged/failed',
        expected_metadata_controls=host.EXPECTED,prospective_additional_bytes=G,inside_additional_bytes=0,
        bootstrap=host.digest(local.inspection_payload().encode()),inherited_local_limits=guard.inherited_limits(),
        print_axioms='N/A; no theorem or Lean execution',both_deployed_targets='not established',
        counterfactual_evaluations=0,unchanged_ordered_events_replayed=0,
        retained_obligations=['first inspection does not establish unit absence; StartTransientUnit failure is terminal',
            'coordination label is inherited source, not evidence of current other-worker absence',
            'fresh epoch allocation and current reservation/identity/runtime checks required',
            'sampled 512MiB guard is not continuous guarantee', '1GiB marker cannot authorize larger consumers'])
    with (OUT/'ResourceMeta1G-source-manifest.json').open('x') as stream:
        json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')

if __name__=='__main__':
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ResourceMeta1GTests))
    if result.wasSuccessful():seal()
    raise SystemExit(0 if result.wasSuccessful() else 1)

