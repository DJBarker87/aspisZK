"""Focused terminal receiver/compact receipt boundary fixtures. No live boundaries."""
import importlib.util,json,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
D=ROOT/'tools/prover-rw-20261023/final-native-gate'
sys.path.insert(0,str(D))
import FinalNativeGate_compact as compact
spec=importlib.util.spec_from_file_location('retained_v4_mocks',D/'FinalNativeGate-v4-tests.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old);old.R=D/'prospective-data-v5'

class Boundary(unittest.TestCase):
    def test_receipts_combined_bound_keeps_small_truthful_failure(self):
        # Projection just under bound plus receipts crosses it; old record must
        # not be retained oversized after the exception.
        r=dict(phase='go',allowed=True,reporting_failed=False,padding='x'*(compact.LIMIT-130))
        with self.assertRaisesRegex(ValueError,'64KiB'):
            compact.receipt(r,[dict(name='go-report.json',size=14107502,sha256='a'*64)])
        self.assertLess(len(json.dumps(r)),compact.LIMIT)
        self.assertIsNone(r['allowed']);self.assertTrue(r['reporting_failed']);self.assertIn('sha256',r)

    def test_fixed_five_receiver_files_expose_denied_parent_without_child(self):
        ns,tree=old.Release().packet()
        packet=ns['STAGE']+'/FinalNativeGate-setup-packet/'
        for name in ('FinalNativeGate-setup-terminal.json','FinalNativeGate-candidate-controls.json'):
            del tree.nodes[packet+name]
        terminal=dict(failed=True,errors=['setup prospective admission denied'],unresolved=False,
                      spawn_state='not_started',admission=[compact.project('prospective',dict(decision=dict(allowed=False,error='exact future cause',cap_ok=False)))])
        tree.nodes[packet+'FinalNativeGate-setup-parent-terminal.json']['raw']=bytearray(json.dumps(terminal).encode())
        result=ns['packet_summary']()
        self.assertEqual(len(result),5);self.assertIn('error',result['FinalNativeGate-setup-terminal.json'])
        r=result['FinalNativeGate-setup-parent-terminal.json']['record']
        self.assertTrue(r['failed']);self.assertEqual(r['admission'][0]['decision']['error'],'exact future cause')
        self.assertEqual(r['spawn_state'],'not_started');self.assertFalse(tree.fds)

if __name__=='__main__':unittest.main(verbosity=2)
