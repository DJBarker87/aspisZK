import unittest,copy,json
import NFJ_audit_check as v
class AuditControls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.data=json.loads((v.E/'NFJ_AUDIT.json').read_text());cls.fixtures=json.loads((v.E/'NFJ_FIXTURES.json').read_text())
 def test_positive(self):self.assertTrue(v.check())
 def test_missing_root(self):
  d=copy.deepcopy(self.data);d['results'].pop()
  with self.assertRaises(AssertionError):v.check(d)
 def test_nonstandard_axiom(self):
  d=copy.deepcopy(self.data);d['results'][0]['walked_axioms']=['sorryAx'];d['results'][0]['collect_axioms']=['sorryAx']
  with self.assertRaises(AssertionError):v.check(d)
 def test_unresolved(self):
  d=copy.deepcopy(self.data);d['zero_unresolved']=False
  with self.assertRaises(AssertionError):v.check(d)
 def test_missing_planted_axiom(self):
  f=copy.deepcopy(self.fixtures);f['fixtures'][0]['walked_axioms']=[];f['fixtures'][0]['collect_axioms']=[]
  with self.assertRaises(AssertionError):v.check(self.data,f)
 def test_different_binary(self):
  f=copy.deepcopy(self.fixtures);f['driver_binary_sha256']='0'*64
  with self.assertRaises(AssertionError):v.check(self.data,f)
if __name__=='__main__':unittest.main()
