"""New identity and actual-caller stub checks only; never contacts a host."""
import ast
import builtins
import copy
import json
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import ResourceRssGOv3_host as host
import ResourceRssGOv3_local as local

BASE='abcd149434cdb75308a010954035da44562cfeee'
CAPTURE='evidence/resource-rss-go-v2-20261025/runtime-inspection.json'

def fixture():
    raw=subprocess.check_output(['git','show',BASE+':'+CAPTURE],cwd=local.ROOT)
    assert host.digest(raw)==dict(sha256='b72b2cd219188c00e5dbb7796b277a3384611762266cd1ca9c40476c63abd669',size=111303)
    # Immutable captured runtime is stored ONLY within a temporary fixture.
    with tempfile.TemporaryDirectory(prefix='ResourceRssGOv3-runtime-') as tmp:
        p=Path(tmp)/'retained-runtime.json';p.write_bytes(raw);info=json.loads(p.read_text())
    tree=ast.parse(local.inspection_payload())
    values=[k.value for n in ast.walk(tree) if isinstance(n,ast.Call) for k in n.keywords if k.arg=='limit_platform']
    assert len(values)==1
    info['limit_platform']=eval(compile(ast.Expression(values[0]),'ResourceRssGOv3-wire','eval'),
        {'sys':SimpleNamespace(platform='linux'),'resource':SimpleNamespace(RLIM_INFINITY=-1)})
    return info

class Focused(unittest.TestCase):
    def setUp(self):self.limits=host.inherited_limits()
    def tearDown(self):self.assertEqual(host.inherited_limits(),self.limits)

    def test_new_identity_exact_bootstrap_and_strict_wire(self):
        self.assertEqual(sys.platform,'darwin')
        self.assertEqual(host.EPOCH,'ResourceRssGOv3-20261025-epoch1')
        self.assertEqual(host.UNIT,'resource-rss-go-v3-20261025')
        self.assertEqual(host.STAGE,'/home/dombarker/project-offloads/codex-cx-resource-rss-go-v3-20261025')
        self.assertEqual(local.OUT,local.ROOT/'evidence/resource-rss-go-v3-20261025')
        original=builtins.__import__;tree=ast.parse(local.inspection_payload())
        runtime=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='runtime_pins')
        runtime.body=ast.parse("raise AssertionError('Linux inventory must not run on Darwin')").body
        def isolated(name,*a,**k):
            if name.startswith('ResourceRssGO'):raise AssertionError('unstaged job import')
            return original(name,*a,**k)
        namespace={}
        with patch.object(builtins,'__import__',isolated),self.assertRaisesRegex(host.GuardError,'unsupported remote Linux'):
            exec(compile(ast.fix_missing_locations(tree),'ResourceRssGOv3-bootstrap-stub','exec'),namespace)
        self.assertNotIn('limits',namespace)
        info=fixture();local.check_remote_linux_limits(info,info['inherited_limits'])
        host.check_limits(self.limits,self.limits)
        for name in ('RLIMIT_AS','RLIMIT_DATA'):
            for side in (0,1):
                for value in (0,4096,resource.RLIM_INFINITY,True,-1.0):
                    bad=copy.deepcopy(info);bad['inherited_limits'][name][side]=value
                    with self.assertRaises(host.GuardError):local.check_remote_linux_limits(bad)
        bad=copy.deepcopy(info);bad['limit_platform']['platform']='darwin'
        with self.assertRaises(host.GuardError):local.check_remote_linux_limits(bad)
        expected=copy.deepcopy(info['inherited_limits']);expected['RLIMIT_CPU']=[True,True]
        with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info,expected)
        expected=copy.deepcopy(info['inherited_limits']);expected['RLIMIT_FUTURE']=[-1,-1]
        with self.assertRaises(host.GuardError):local.check_remote_linux_limits(info,expected)

    def test_actual_inspect_charge_and_no_retry(self):
        code=local.inspection_payload()
        for mode in ('success','wrong-wire','ownership','transport-exit','transport-error'):
            with self.subTest(mode=mode),tempfile.TemporaryDirectory(prefix='ResourceRssGOv3-inspect-') as tmp:
                out=Path(tmp);info=fixture();calls=[]
                if mode=='wrong-wire':info['limit_platform']['rlim_infinity']=resource.RLIM_INFINITY
                if mode=='ownership':info['parent_uid']=info['uid']+1
                def transport(payload,label):
                    self.assertTrue((out/'ATTEMPTED').exists());self.assertEqual(payload,code)
                    calls.append(label)
                    if mode=='transport-error':raise OSError('controlled transport failure')
                    return SimpleNamespace(returncode=1 if mode=='transport-exit' else 0,stdout=json.dumps(info))
                with patch.object(local,'OUT',out),patch.object(local,'ssh_python',transport):
                    if mode=='success':local.inspect()
                    else:
                        with self.assertRaises((RuntimeError,ValueError,OSError)):local.inspect()
                    with self.assertRaises(FileExistsError):local.inspect()
                self.assertEqual(calls,['inspect'])
                self.assertEqual({p.name for p in out.iterdir()}, {'ATTEMPTED','runtime-inspection.json'} if mode in ('success','wrong-wire') else {'ATTEMPTED'})

    def test_actual_stage_rejects_saved_wrong_wire_before_sources_or_ssh(self):
        with tempfile.TemporaryDirectory(prefix='ResourceRssGOv3-stage-') as tmp:
            out=Path(tmp);info=fixture();info['limit_platform']['rlim_infinity']=True
            (out/'runtime-inspection.json').write_text(json.dumps(info))
            with patch.object(local,'OUT',out),patch.object(local,'sources',side_effect=AssertionError('packaging reached')) as package,patch.object(local,'ssh_python',side_effect=AssertionError('SSH reached')) as transport:
                with self.assertRaises(host.GuardError):local.stage()
                package.assert_not_called();transport.assert_not_called()
            self.assertEqual({p.name for p in out.iterdir()},{'runtime-inspection.json'})

    def test_retained_missing_first_inspection_unit_obligation(self):
        tree=ast.parse(local.inspection_payload())
        # The exact payload's executable top level contains platform/limits,
        # stage/parent/lock metadata only. No unit query or scope path appears.
        top=[n for n in tree.body if not isinstance(n,(ast.FunctionDef,ast.ClassDef,ast.Import,ast.ImportFrom))]
        text='\n'.join(ast.unparse(n) for n in top)
        self.assertNotIn(host.UNIT,text);self.assertNotIn('systemctl',text)
        self.assertNotIn('/sys/fs/cgroup',text)
        self.assertNotIn('scope_exists',text)
        # Actual caller checks only stage_exists and uid/parent_uid before save.
        inspect=next(n for n in ast.parse(Path(local.__file__).read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='inspect')
        condition=next(n.test for n in inspect.body if isinstance(n,ast.If) and 'stage_exists' in ast.unparse(n.test))
        self.assertEqual(ast.unparse(condition), "info['stage_exists'] or info['uid'] != info['parent_uid']")
        # Unit absence is not established. This is not a claim of actual collision.

if __name__=='__main__':unittest.main(verbosity=2)
