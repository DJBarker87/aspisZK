"""Static comparison-boundary mutations plus unchanged inherited test suite."""
import unittest,copy,json,lzma
import NFH_validate as v
import NFD_validator_tests as prior
class Boundary(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.dis=lzma.decompress((v.E/'NFH_default_disassembly.txt.xz').read_bytes()).decode()
  cls.rel=(v.E/'NFH_default_relocations.txt').read_text()
  cls.packet=json.loads((v.E/'NFH_LEDGER_DELTA.json').read_text())
 def test_wrapper(self):self.assertFalse(v.wrapper_check(self.dis,self.rel)['runtime_body_visible'])
 def test_sites(self):self.assertEqual(v.callsite_check(self.dis)['size'],688)
 def test_both_artifacts(self):self.assertEqual(set(v.artifacts()),{'default','devnet'})
 def test_every_wrapper_instruction_mutation(self):
  for i,original in enumerate(v.WRAPPER):
   with self.subTest(i=i):
    addr=0x1749d0+8*i
    changed=self.dis.replace(f'{addr:x}: '+original,f'{addr:x}: '+'00 '*7+'00')
    self.assertNotEqual(changed,self.dis)
    with self.assertRaises(AssertionError):v.wrapper_check(changed,self.rel)
 def test_wrong_runtime_symbol(self):
  with self.assertRaises(AssertionError):v.wrapper_check(self.dis,self.rel.replace('sol_memcmp_','sol_memcpy_'))
 def test_wrong_result_slot(self):
  with self.assertRaises(AssertionError):v.wrapper_check(self.dis,self.rel.replace('00000000001749e8','00000000001749e0'))
 def test_wrong_buffer(self):
  with self.assertRaises(AssertionError):v.callsite_check(self.dis.replace('4ab50: bf 72','4ab50: bf 82'))
 def test_wrong_length(self):
  with self.assertRaises(AssertionError):v.callsite_check(self.dis.replace('4ab58: b7 03 00 00 b0 02','4ab58: b7 03 00 00 b1 02'))
 def test_wrong_zero_test(self):
  with self.assertRaises(AssertionError):v.callsite_check(self.dis.replace('4ab78: 55 00','4ab78: 15 00'))
 def test_empty_delta_preserves_base(self):
  base={'sentinel':[1]};out=v.compose(base,self.packet);self.assertEqual(base,out);self.assertIsNot(base,out)
 def test_no_unapproved_promotion(self):
  changes={'new_closed_rows':1,'new_closed_edges':1,'new_closed_roots':1,'NFH_certificates':{'scanner':True},'new_trust_adopted':['RuntimeMemcmp688Zero'],'scanner_status':'CLOSED','native_equality_bridge_discharged':True}
  for k,value in changes.items():
   with self.subTest(k=k):
    p=copy.deepcopy(self.packet);p[k]=value
    with self.assertRaises(AssertionError):v.packet_check(p)

def load_tests(loader,tests,pattern):
 tests.addTests(loader.loadTestsFromModule(prior));return tests
if __name__=='__main__':unittest.main()
