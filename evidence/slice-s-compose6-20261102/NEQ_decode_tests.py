import unittest,copy,json,hashlib
import NEQ_validate as v
from NEQ_decode_checks import FUNCTIONS,validate
class DecodeGates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json')
 def mutate(self,fn):
  for f in FUNCTIONS.values():
   c=copy.deepcopy(self.p['members'][f]);fn(c['decode_scalar']);self.assertFalse(validate(c,f,self.b,v))
 def test_positive(self):
  for f in FUNCTIONS.values():self.assertTrue(validate(self.p['members'][f],f,self.b,v))
 def test_missing_native_control(self):self.mutate(lambda q:q['pairs'].pop())
 def test_missing_model_law(self):self.mutate(lambda q:q['theorems'].pop())
 def test_hidden_acceptance(self):self.mutate(lambda q:q['inner_hypotheses_remaining'].append('accepted'))
 def test_missing_frame(self):self.mutate(lambda q:q.__setitem__('empty_external_modifies',False))
 def test_missing_return_variant(self):self.mutate(lambda q:q.__setitem__('all_return_variants',False))
 def test_wrong_source(self):self.mutate(lambda q:q.__setitem__('frozen_body',q['frozen_body']+' '))
 def test_wrong_digest_word_inputs(self):
  f=FUNCTIONS['digest'];c=copy.deepcopy(self.p['members'][f]);c['decode_scalar']['same_child_input']='fresh independent words';self.assertFalse(validate(c,f,self.b,v))
 def test_missing_child_keeps_digest_open(self):
  p=copy.deepcopy(self.p);del p['members'][FUNCTIONS['m31']];out=v.compose(self.b,p,self.r);rows=[r for r in out['rows'] if r['function']==FUNCTIONS['digest']];self.assertTrue(rows);self.assertTrue(all(r['composed_status']=='OPEN' for r in rows))
if __name__=='__main__':unittest.main(verbosity=2)
