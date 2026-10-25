"""Affected parent lifecycle/order plus persistent guard integration; mock OS only."""
import importlib.util
from pathlib import Path
import sys
import unittest
from unittest.mock import Mock
E=Path(__file__).resolve().parent
D=E.parents[3]/'tools/prover-rw-20261023/final-native-gate'
sys.path.insert(0,str(D))
import FinalNativeGate_guard as g
spec=importlib.util.spec_from_file_location('source_v5_lifecycle',D/'FinalNativeGate-v5-tests.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Persistent(unittest.TestCase):
    def test_persistent_thread_ready_and_final_sample_with_same_owned_root(self):
        p=Mock();p.events=[];p.optional.return_value=dict(pid=12,ppid=1,tgid=12,starttime=99,rss_bytes=123)
        p.children.return_value=set();notify=Mock();guard=g.Guard(proc=p,pid=12,notify=notify)
        guard.start();thread=guard.thread
        guard.check();guard.check();receipt=guard.finish()
        self.assertIs(guard.thread,thread);self.assertFalse(thread.is_alive());notify.assert_not_called()
        self.assertGreaterEqual(len(receipt['samples']),2);self.assertEqual(receipt['budget_bytes'],4*2**30)
        self.assertEqual(receipt['proc_events'],[])
if __name__=='__main__':
    suite=unittest.TestSuite()
    for cls in (Persistent,m.Lifecycle,m.V5Order):suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(cls))
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(not result.wasSuccessful())
