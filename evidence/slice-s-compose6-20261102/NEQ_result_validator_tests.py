import unittest,copy,json,hashlib
import NEQ_validate as v
from NEQ_result_validator_checks import F,validate
class ResultValidatorGate(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json');cls.c=cls.p['members'][F]
 def test_positive(self):self.assertTrue(validate(self.c,F,self.b,v))
 def bad(self,fn):
  c=copy.deepcopy(self.c);fn(c['result_validator']);self.assertFalse(validate(c,F,self.b,v))
 def test_missing_child_place_control(self):self.bad(lambda q:q['pairs'].pop())
 def test_missing_model_theorem(self):self.bad(lambda q:q['theorems'].pop())
 def test_stronger_domain(self):self.bad(lambda q:q.__setitem__('domain','canonical result only'))
 def test_hidden_inner_hypothesis(self):self.bad(lambda q:q['inner_hypotheses_remaining'].append('After.PacketDomain'))
 def test_missing_Result(self):self.bad(lambda q:q.__setitem__('full_Result',False))
 def test_missing_effect_order(self):self.bad(lambda q:q.__setitem__('ordered_effects',False))
 def test_missing_frame(self):self.bad(lambda q:q.__setitem__('empty_external_modifies',False))
 def test_missing_receipt(self):self.bad(lambda q:q['native_support'].pop())
 def test_wrong_frozen_source(self):self.bad(lambda q:q.__setitem__('frozen_body',q['frozen_body'].replace('result.output_lane != expected','result.output_lane == expected')))
 def test_refreshed_review_wrong_prestate(self):
  c=copy.deepcopy(self.c);c['call_domain_certificate']['same_prestate']=False;c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r=copy.deepcopy(self.r);r[F]=h;self.assertFalse(v.certificate(c,F,self.b,r))
class ResultValidatorComposition(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json')
 def assert_open(self,p,r):
  out=v.compose(self.b,p,r);rows=[x for x in out['rows'] if x['function']==F];self.assertTrue(rows);self.assertTrue(all(x['composed_status']=='OPEN' for x in rows))
 def test_missing_member_keeps_open(self):
  p=copy.deepcopy(self.p);del p['members'][F];self.assert_open(p,self.r)
 def test_wrong_edge_keeps_open(self):
  p=copy.deepcopy(self.p);r=copy.deepcopy(self.r);k=F+' -> crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1';c=p['edges'][k];c['call_domain_certificate']['same_arguments']=False;c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r[k]=h;self.assert_open(p,r)
if __name__=='__main__':unittest.main(verbosity=2)
