"""Tiny offline simulations; never execute the real scan or live interfaces."""
import ast, copy, hashlib, io, json, resource, subprocess, sys, time, types, unittest, weakref, gc
from pathlib import Path
start = time.monotonic()
REV = '9fe9f199d1e52e3dcf4b355dff57330e5019a220'
STAT = subprocess.check_output(['git','rev-parse','5756082d']).decode().strip()
def immutable(rev, path):
    return subprocess.check_output(['git','show',rev+':'+path]).decode()
def module(name, source):
    m=types.ModuleType(name);sys.modules[name]=m
    exec(compile(source,'<offline-'+name+'>','exec'),m.__dict__)
    return m
source=Path(__file__).with_name('ResourceCaptureRetry_candidate.py').read_text()
base=immutable(REV,'tools/resource-snapshot-20261025/ResourceSnapshot_candidate.py')
c=module('ResourceAvailable_candidate',source)
# Hard interlock: all tests must inject a fake scan_once.
def forbidden(*args,**kwargs): raise AssertionError('real scan forbidden')
c.scan_once=forbidden
r='fbe04424e7553d9b0844ae19c2206b15cf3dd831'
go_source=immutable(r,'tools/resource-available-20261024/ResourceAvailable_go.py')
go=module('ResourceAvailable_go',go_source)
generic_source=immutable(r,'tools/resource-available-20261024/ResourceAvailable_tests.py')
generic=module('original_tests',generic_source)
# Original parser tests target scan directly, with Path.read_text patched; keep
# parser coverage but forbid their scan from proceeding into hierarchy traversal.
original_scan=c.scan
original_once=module('base_offline',base).scan
class RetryTests(unittest.TestCase):
    def exercise(self,n):
        s=generic.fixture();s.update(raw_inputs={'fresh':'only'},read_attempts=[])
        expected=c.observe(s);calls=[];refs=[]
        class Payload: pass
        def fake(root):
            calls.append(root)
            if len(calls)<=n:
                payload=Payload();refs.append(weakref.ref(payload))
                e=OSError(2 if len(calls)%2 else 3,'gone','/proc/42/stat')
                e.partial_raw_inputs={'failed':payload};e.read_attempts=[{'failed':True}]
                raise e
            return s
        c.scan_once=fake
        root=Path('/fake-root');out=c.scan(root)
        self.assertIs(out,s);self.assertEqual(calls,[root]*(n+1))
        self.assertEqual(c.observe(out),expected)
        self.assertEqual(out['read_attempts'],[])
        self.assertEqual(out['raw_inputs'],{'fresh':'only'})
        self.assertEqual(len(out['discarded_scan_failures']),n)
        self.assertTrue(out['discarded_all_inputs'])
        gc.collect();self.assertTrue(all(ref() is None for ref in refs))
    def test_fresh(self): self.exercise(1)
    def test_fourth(self): self.exercise(3)
    def test_no_failure(self): self.exercise(0)
    def test_exhaustion(self):
        calls=[]
        def fake(root):
            calls.append(root);e=OSError(3,'gone','/proc/9/cgroup')
            e.partial_raw_inputs={'old':'excluded'};raise e
        c.scan_once=fake
        with self.assertRaises(OSError) as caught:c.scan()
        e=caught.exception
        self.assertEqual(len(calls),4);self.assertEqual(len(e.discarded_scan_failures),4)
        self.assertFalse(hasattr(e,'partial_raw_inputs'))
    def test_no_retry(self):
        errors=[OSError(code,'bad',path) for code,path in
            [(2,'/proc/meminfo'),(2,'/proc/self/stat'),(2,'/proc/01/stat'),
             (2,'/proc/0/stat'),(2,'/proc/１２/stat'),(2,'/proc/1/maps'),
             (2,'/proc/1/../stat'),(2,'/sys/fs/cgroup/stat'),(13,'/proc/1/stat'),
             (2,None),(2,b'/proc/1/stat'),(12,'/proc/1/stat')]]
        errors += [ValueError('identity'),MemoryError('cap')]
        for error in errors:
            calls=[]
            def fake(root): calls.append(root);raise error
            c.scan_once=fake
            with self.assertRaises(type(error)) as caught:c.scan()
            self.assertIs(caught.exception,error);self.assertEqual(len(calls),1)
    def test_all_metadata_files(self):
        for name in ('stat','status','cgroup'):
            for code in (2,3):
                calls=[]
                def fake(root):
                    calls.append(root)
                    if len(calls)==1:raise OSError(code,'gone','/proc/123/'+name)
                    return {}
                c.scan_once=fake
                self.assertEqual(len(c.scan()['discarded_scan_failures']),1)
    def test_source_exact(self):
        a=ast.parse(base);b=ast.parse(source)
        old=next(n for n in a.body if isinstance(n,ast.FunctionDef) and n.name=='scan')
        once=next(n for n in b.body if isinstance(n,ast.FunctionDef) and n.name=='scan_once')
        self.assertEqual(ast.get_source_segment(base,old).replace('def scan(', 'def scan_once(',1),ast.get_source_segment(source,once))
        b.body=[n for n in b.body if not(isinstance(n,ast.FunctionDef) and n.name=='scan')]
        once.name='scan';self.assertEqual(ast.dump(a),ast.dump(b))

def run(case):
    stream=io.StringIO();result=unittest.TextTestRunner(stream=stream,verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(case))
    return dict(tests=result.testsRun,successful=result.wasSuccessful(),output=stream.getvalue())
focused=run(RetryTests)
# Reuse all 16 original tests with original parser callable ONLY under mocked
# read_text. Guard independently against any real filesystem read in that call.
def parser_only(root=Path('/sys/fs/cgroup')):
    from unittest.mock import Mock
    assert isinstance(Path.read_text,Mock), 'parser requires mocked read_text'
    return original_once(root)
c.scan=parser_only
original=run(generic.ResourceAvailableTests)
c.scan=original_scan;c.scan_once=forbidden
stat_source=immutable(STAT,'tools/resource-stat-20261024/ResourceStat_go.py')
stat_tree=ast.parse(stat_source)
scan_bound=ast.get_source_segment(stat_source,next(n for n in stat_tree.body if isinstance(n,ast.FunctionDef) and n.name=='scan_bound'))
assert "snapshot = base['scan']()" in scan_bound
assert scan_bound.index('first = self_observation()') < scan_bound.index("snapshot = base['scan']()") < scan_bound.index('second = self_observation()')
wrapper=ast.get_source_segment(source,next(n for n in ast.parse(source).body if isinstance(n,ast.FunctionDef) and n.name=='scan'))
def pin(s):return dict(size_bytes=len(s.encode()),sha256=hashlib.sha256(s.encode()).hexdigest())
usage=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(mode='source-only fake scans; original parser uses mocked reads',exit=0 if focused['successful'] and original['successful'] else 1,focused=focused,original16=original,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,swaps=usage.ru_nswap,local_limit_bytes=512*2**20,print_axioms='N/A; compiler/formal budget 0',source_pins=dict(base_revision=REV,base=pin(base),candidate=pin(source),stat_revision=STAT,stat_go=pin(stat_source),scan_bound=pin(scan_bound),generic_revision=r,generic=pin(generic_source),go=pin(go_source)),scan_wrapper_source=wrapper,scan_wrapper_function_sha256=pin(wrapper)['sha256'],needs_scan_once_original_alias=True,both_security_targets='NOT ESTABLISHED',execution_grant=False)
assert receipt['peak_rss_bytes']<=512*2**20
Path('evidence/resource-capture-retry-20261025/tests.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2));sys.exit(receipt['exit'])
