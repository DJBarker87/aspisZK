import unittest,copy
import NEQ_validate as v
import NEQ_unwrap_checks as u,NEQ_common_decode_checks as d
class CommonGates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json')
 def test_positive(self):
  for x in [u,d]:self.assertTrue(x.validate(self.p['members'][x.F],x.F,self.b,v))
 def bad(self,x,key,fn):
  c=copy.deepcopy(self.p['members'][x.F]);fn(c[key]);self.assertFalse(x.validate(c,x.F,self.b,v))
 def test_missing_unwrap_borrow_control(self):self.bad(u,'unwrap_conversion',lambda q:q['pairs'].pop())
 def test_missing_generic_model(self):self.bad(u,'unwrap_conversion',lambda q:q['theorems'].pop())
 def test_wrong_owned_carrier(self):self.bad(u,'unwrap_conversion',lambda q:q.__setitem__('same_owned_or_borrowed_carrier',False))
 def test_wrong_common_borrow(self):self.bad(d,'common_decode',lambda q:q.__setitem__('same_borrowed_digest_places',False))
 def test_missing_full_Result(self):self.bad(d,'common_decode',lambda q:q.__setitem__('full_Result',False))
 def test_wrong_common_source(self):self.bad(d,'common_decode',lambda q:q.__setitem__('frozen_body','invalid source'))
 def test_missing_common_control(self):self.bad(d,'common_decode',lambda q:q['pairs'].pop())
 def test_hidden_inner_domain(self):self.bad(d,'common_decode',lambda q:q['inner_hypotheses_remaining'].append('Digest.PacketDomain'))
 def test_missing_conversion_keeps_common_open(self):
  p=copy.deepcopy(self.p);del p['members'][u.F];out=v.compose(self.b,p,self.r);rows=[r for r in out['rows'] if r['function']==d.F];self.assertTrue(rows);self.assertTrue(all(r['composed_status']=='OPEN' for r in rows))
if __name__=='__main__':unittest.main(verbosity=2)
