"""Focused offline Linux-capture / Darwin-inspector boundary regressions."""
import ast
import builtins
import copy
import json
from pathlib import Path
import resource
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import ResourceRssGOv2_local as local
import ResourceRssGOv2_host as host

OUT=local.OUT


def retained():
    return json.loads((OUT/'runtime-inspection.json').read_text())


def wire_info():
    # Evaluate the EXACT generated metadata expression with controlled source
    # values; never execute Linux inventory or mutate local sys/resource state.
    tree=ast.parse(local.inspection_payload())
    fields=[k.value for n in ast.walk(tree) if isinstance(n,ast.Call)
            for k in n.keywords if k.arg=='limit_platform']
    assert len(fields)==1
    metadata=eval(compile(ast.Expression(fields[0]),'PORTABILITY-metadata','eval'),
                  {'sys':SimpleNamespace(platform='linux'),
                   'resource':SimpleNamespace(RLIM_INFINITY=-1)})
    info=retained();info['limit_platform']=metadata
    return info


class PortabilityTests(unittest.TestCase):
    def setUp(self):
        self.limits=host.inherited_limits()
        self.assertEqual(sys.platform,'darwin')
        self.assertEqual(resource.RLIM_INFINITY,9223372036854775807)

    def tearDown(self):
        self.assertEqual(host.inherited_limits(),self.limits)

    def test_retained_boundary_and_immutable_old_failure(self):
        info=wire_info();before=copy.deepcopy(info)
        local.check_remote_linux_limits(info,info['inherited_limits'])
        self.assertEqual(info,before)
        # Frozen historical function, not new code relabelled as old evidence.
        raw=(OUT/'ResourceRssGOv2_guard.py.after.py.txt').read_text()
        tree=ast.parse(raw)
        fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='check_limits')
        namespace={'resource':resource,'GuardError':host.GuardError}
        exec(compile(ast.Module(body=[fn],type_ignores=[]),'PORTABILITY-old-checker','exec'),namespace)
        with self.assertRaisesRegex(host.GuardError,'unexpected inherited restriction: RLIMIT_AS'):
            namespace['check_limits'](retained()['inherited_limits'])
        # LOCAL checks continue to use the actual LOCAL constant.
        host.check_limits(self.limits,self.limits)

    def test_finite_as_data_and_exact_wire_types(self):
        for name in ('RLIMIT_AS','RLIMIT_DATA'):
            for index in (0,1):
                for value in (0,1,4096,-2,-99,9223372036854775807,True,False,1.0,'-1',None):
                    with self.subTest(name=name,index=index,value=value):
                        info=wire_info();info['inherited_limits'][name][index]=value
                        with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)
        for pair in ([],[-1],[-1,-1,-1],(-1,-1),'-1',None,True,{'soft':-1,'hard':-1}):
            info=wire_info();info['inherited_limits']['RLIMIT_AS']=pair
            with self.subTest(pair=pair),self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)
        for value in (-2,True,False,1.0,'1',None):
            info=wire_info();info['inherited_limits']['RLIMIT_CPU']=[value,value]
            with self.subTest(other=value),self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)

    def test_fixed_metadata_schema_and_missing_fields(self):
        for key in ('platform','rlim_infinity'):
            info=wire_info();del info['limit_platform'][key]
            with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)
        for metadata in (None,{},[],{'platform':'linux','rlim_infinity':-1,'extra':0},
                         {'platform':'darwin','rlim_infinity':-1},
                         {'platform':'linux2','rlim_infinity':-1}):
            info=wire_info();info['limit_platform']=metadata
            with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)
        for value in (9223372036854775807,-2,0,True,False,-1.0,'-1',None):
            info=wire_info();info['limit_platform']['rlim_infinity']=value
            with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)
        for key in ('limit_platform','inherited_limits'):
            info=wire_info();del info[key]
            with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)
        for name in ('RLIMIT_AS','RLIMIT_DATA'):
            info=wire_info();del info['inherited_limits'][name]
            with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)
        for limits in (None,[],True,{'bad':[0,0]},{1:[0,0]}):
            info=wire_info();info['inherited_limits']=limits
            with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info)

    def test_whole_map_exactness_including_unlimited_and_missing(self):
        info=wire_info();limits=info['inherited_limits']
        for name,pair in limits.items():
            for index in (0,1):
                expected=copy.deepcopy(limits)
                expected[name][index]=0 if pair[index]==-1 else pair[index]+1
                with self.subTest(name=name,index=index),self.assertRaises(host.GuardError):
                    local.check_remote_linux_limits(info,expected)
            expected=copy.deepcopy(limits);del expected[name]
            with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info,expected)
        expected=copy.deepcopy(limits);expected['RLIMIT_FUTURE']=[-1,-1]
        with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info,expected)
        expected=copy.deepcopy(limits);expected['RLIMIT_CPU']=[True,True]
        with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info,expected)
        # The deployed host's whole-map comparator is unchanged and still rejects
        # mismatch on an unlimited cell when supplied genuine local constants.
        expected=copy.deepcopy(self.limits);expected['RLIMIT_CPU']=[0,0]
        with self.assertRaisesRegex(host.GuardError,'changed'):host.check_limits(self.limits,expected)

    def test_exact_bootstrap_forbidden_job_imports_and_darwin_fail_closed(self):
        code=local.inspection_payload();tree=ast.parse(code)
        original=builtins.__import__
        def isolated(name,*args,**kwargs):
            if name.startswith('ResourceRssGOv2'):raise AssertionError('job import in bootstrap')
            return original(name,*args,**kwargs)
        # The sole function stub is Linux runtime inventory; it must never be
        # reached on Darwin. No fake getrlimit, resource module or platform.
        runtime=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='runtime_pins')
        runtime.body=ast.parse("raise AssertionError('Linux inventory executed on Darwin')").body
        namespace={}
        with patch.object(builtins,'__import__',isolated):
            with self.assertRaisesRegex(RuntimeError,'unsupported remote Linux resource platform'):
                exec(compile(ast.fix_missing_locations(tree),'PORTABILITY-exact-bootstrap','exec'),namespace)
        self.assertNotIn('limits',namespace)
        # Exact remote prefix must guard platform before limit capture/inventory.
        statements=[ast.unparse(n) for n in tree.body]
        guard=next(i for i,s in enumerate(statements) if s.startswith("if sys.platform != 'linux'"))
        capture=statements.index('limits = inherited_limits()')
        self.assertLess(guard,capture)
        self.assertEqual(statements[capture+1],'check_limits(limits)')
        self.assertEqual(wire_info()['limit_platform'],{'platform':'linux','rlim_infinity':-1})
        # Evaluate the exact generated platform predicate on controlled values,
        # without stubbing any runtime function or modifying sys/resource.
        predicate=tree.body[guard].test
        for platform,infinity,reject in (
            ('linux',-1,False),('darwin',-1,True),('linux2',-1,True),
            ('linux',9223372036854775807,True),('linux',-2,True),
            ('linux',True,True),('linux',-1.0,True),('linux','-1',True)):
            with self.subTest(platform=platform,infinity=infinity):
                actual=eval(compile(ast.Expression(predicate),'PORTABILITY-platform-predicate','eval'),
                            {'sys':SimpleNamespace(platform=platform),
                             'resource':SimpleNamespace(RLIM_INFINITY=infinity)})
                self.assertIs(actual,reject)

    def test_actual_inspect_caller_charge_transport_and_terminal_failures(self):
        code=local.inspection_payload()
        for mode in ('success','exit','exception','invalid-wire','ownership'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory(prefix='PORTABILITY-') as tmp:
                directory=Path(tmp);calls=[];info=wire_info()
                if mode=='invalid-wire':info['limit_platform']['rlim_infinity']=resource.RLIM_INFINITY
                if mode=='ownership':info['stage_exists']=True
                def transport(payload,label):
                    self.assertTrue((directory/'ATTEMPTED').exists())
                    self.assertEqual(payload,code);self.assertEqual(label,'inspect')
                    calls.append(label)
                    if mode=='exception':raise OSError('controlled transport failure')
                    return SimpleNamespace(returncode=1 if mode=='exit' else 0,stdout=json.dumps(info))
                with patch.object(local,'OUT',directory),patch.object(local,'ssh_python',transport):
                    if mode=='success':local.inspect()
                    else:
                        with self.assertRaises((RuntimeError,OSError,ValueError)):local.inspect()
                    # Charge remains after every terminal path. Second invocation
                    # cannot transport, and is not an implicit retry.
                    with self.assertRaises(FileExistsError):local.inspect()
                self.assertEqual(calls,['inspect'])
                names={p.name for p in directory.iterdir()}
                self.assertEqual(names,{'ATTEMPTED','runtime-inspection.json'} if mode in ('success','invalid-wire') else {'ATTEMPTED'})
                if mode=='success':
                    self.assertEqual(json.loads((directory/'runtime-inspection.json').read_text()),info)
                self.assertNotIn('manifest.json',names);self.assertNotIn('RUN_ATTEMPTED',names)
        # Local stage's saved-map validation is before source packaging/transport;
        # no stage/preflight/run/export call is executed by this suite.
        tree=ast.parse(Path(local.__file__).read_text())
        stage=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='stage')
        self.assertEqual(ast.unparse(stage.body[1]),'check_remote_linux_limits(info)')
        self.assertEqual(ast.unparse(stage.body[2]),'files = sources()')

if __name__=='__main__':unittest.main(verbosity=2)
