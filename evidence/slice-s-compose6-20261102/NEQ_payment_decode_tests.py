import unittest,copy
import NEQ_validate as v
from NEQ_payment_decode_checks import FUNCTIONS,validate
class PaymentGates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json')
 def bad(self,fn):
  for f in FUNCTIONS.values():
   c=copy.deepcopy(self.p['members'][f]);fn(c['payment_decode']);self.assertFalse(validate(c,f,self.b,v))
 def test_positive(self):
  for f in FUNCTIONS.values():self.assertTrue(validate(self.p['members'][f],f,self.b,v))
 def test_missing_guard_pair(self):self.bad(lambda q:q['pairs'].pop())
 def test_missing_guard_theorem(self):self.bad(lambda q:q['theorems'].pop(2))
 def test_claimed_ZST_identity_rejected(self):self.bad(lambda q:q.__setitem__('zst_pointer_identity_claimed',True))
 def test_missing_byte_place_rejected(self):self.bad(lambda q:q.__setitem__('nonzero_byte_places_proved',False))
 def test_wrong_guard_shape(self):self.bad(lambda q:q.__setitem__('guard_shape','Unit pointer identity'))
 def test_missing_full_Result(self):self.bad(lambda q:q.__setitem__('full_Result',False))
 def test_hidden_acceptance(self):self.bad(lambda q:q['inner_hypotheses_remaining'].append('accepted common'))
 def test_wrong_frozen_source(self):self.bad(lambda q:q.__setitem__('frozen_body',q['frozen_body']+' '))
 def test_missing_child_keeps_both_open(self):
  p=copy.deepcopy(self.p);del p['members']['crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common'];out=v.compose(self.b,p,self.r)
  for f in FUNCTIONS.values():
   rows=[r for r in out['rows'] if r['function']==f];self.assertTrue(rows);self.assertTrue(all(r['composed_status']=='OPEN' for r in rows))
if __name__=='__main__':unittest.main(verbosity=2)
