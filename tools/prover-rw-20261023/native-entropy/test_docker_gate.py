"""No Docker/build launched: test the actual job-owned release function."""
from pathlib import Path
import importlib.util,json,tempfile,unittest
s=importlib.util.spec_from_file_location('docker_gate',Path(__file__).with_name('docker_gate.py'))
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)

class BarrierTests(unittest.TestCase):
    def setUp(self):
        self.t=tempfile.TemporaryDirectory();self.addCleanup(self.t.cleanup)
        self.root=Path(self.t.name);self.cg=self.root/'cg';self.cg.mkdir()
        self.out=self.root/'out';self.out.mkdir()
        for key,value in {'memory.high':6*2**30,'memory.max':8*2**30,'memory.swap.max':0,'pids.max':64}.items():
            (self.cg/key).write_text(str(value))
    def test_go_requires_exact_caps(self):
        for key in ['memory.high','memory.max','memory.swap.max','pids.max']:
            previous=(self.cg/key).read_text();(self.cg/key).write_text('max')
            with self.assertRaises(AssertionError):m.release(self.cg,self.out,lambda **_:self.fail('admission before caps'))
            self.assertFalse((self.out/'go').exists());(self.cg/key).write_text(previous)
    def test_live_denial_no_go(self):
        def check(requested):
            self.assertEqual(requested,0);self.assertFalse((self.out/'go').exists())
            return dict(allowed=False,error='fixture unreadable')
        with self.assertRaises(AssertionError):m.release(self.cg,self.out,check)
        self.assertFalse((self.out/'go').exists())
    def test_live_admission_before_go(self):
        def check(requested):
            self.assertEqual(requested,0);self.assertFalse((self.out/'go').exists())
            return dict(allowed=True)
        m.release(self.cg,self.out,check)
        self.assertTrue((self.out/'go').exists())

if __name__=='__main__':unittest.main(verbosity=2)
