import unittest,copy,json,hashlib
import NEQ_validate as v
from NEQ_nullifier_checks import FUNCTIONS,validate
class Nullifier(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json')
 def test_both_positive(self):
  for f in FUNCTIONS.values():self.assertTrue(validate(self.p['members'][f],f,self.b,v))
 def test_wrong_place_keeps_gate_closed(self):
  for f in FUNCTIONS.values():
   c=copy.deepcopy(self.p['members'][f]);c['nullifier_getter']['same_borrowed_place']=False;self.assertFalse(validate(c,f,self.b,v))
 def test_stronger_domain_rejected(self):
  for f in FUNCTIONS.values():
   c=copy.deepcopy(self.p['members'][f]);c['nullifier_getter']['domain']='canonical inputs';self.assertFalse(validate(c,f,self.b,v))
 def test_missing_native_control_rejected(self):
  for f in FUNCTIONS.values():
   c=copy.deepcopy(self.p['members'][f]);c['nullifier_getter']['pairs']=[];self.assertFalse(validate(c,f,self.b,v))
 def test_wrong_frozen_field_rejected(self):
  for f in FUNCTIONS.values():
   c=copy.deepcopy(self.p['members'][f]);c['nullifier_getter']['frozen_body']=c['nullifier_getter']['frozen_body'].replace('public.nullifier','public.anchor_root');self.assertFalse(validate(c,f,self.b,v))
 def test_hidden_borrow_hypothesis_rejected(self):
  for f in FUNCTIONS.values():
   c=copy.deepcopy(self.p['members'][f]);c['nullifier_getter']['inner_hypotheses_remaining']=['place_matches'];self.assertFalse(validate(c,f,self.b,v))
if __name__=='__main__':unittest.main(verbosity=2)
