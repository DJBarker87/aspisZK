import unittest,copy,json,hashlib
import NEQ_validate as v
from NEQ_encoder_checks import F,validate
class EncoderGate(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json');cls.c=cls.p['roots'][F]
 def test_positive(self):self.assertTrue(validate(self.c,F,self.b,v))
 def check_bad(self,change):
  c=copy.deepcopy(self.c);change(c['encoder_root']);self.assertFalse(validate(c,F,self.b,v))
 def test_missing_native_pair(self):self.check_bad(lambda q:q['pairs'].pop())
 def test_wrong_native_pair(self):self.check_bad(lambda q:q['pairs'].__setitem__(0,['NEQ_K002','NEQ_K002']))
 def test_wrong_domain(self):self.check_bad(lambda q:q.__setitem__('domain','canonical successful statements only'))
 def test_hidden_inner_domain(self):self.check_bad(lambda q:q['inner_hypotheses_remaining'].append('Late.PacketDomain'))
 def test_missing_model_theorem(self):self.check_bad(lambda q:q['theorems'].pop(0))
 def test_missing_full_frame(self):self.check_bad(lambda q:q.__setitem__('same_allocation',False))
 def test_wrong_call_order(self):self.check_bad(lambda q:q.__setitem__('ordered_effects',False))
 def test_missing_full_Result(self):self.check_bad(lambda q:q.__setitem__('full_Result',False))
 def test_missing_source_segment(self):self.check_bad(lambda q:q['source_partition'].pop())
 def test_wrong_source_segment(self):self.check_bad(lambda q:q['source_partition'].__setitem__(1,q['source_partition'][1].replace('output[7]','output[8]')))
 def test_missing_native_receipt(self):self.check_bad(lambda q:q['native_support'].pop())
 def test_wrong_loop_invariant(self):self.check_bad(lambda q:q.__setitem__('loop_invariant','single selected child byte'))
 def test_new_trust(self):self.check_bad(lambda q:q.__setitem__('trust_classification','trust removed'))
 def test_refreshed_review_cannot_hide_wrong_prestate(self):
  c=copy.deepcopy(self.c);c['call_domain_certificate']['same_prestate']=False;c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r=copy.deepcopy(self.r);r[F]=h
  self.assertFalse(v.certificate(c,F,self.b,r))
class EncoderComposition(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json')
 def assert_open(self,p,r):
  out=v.compose(self.b,p,r);rows=[x for x in out['rows'] if x['function']==F];self.assertTrue(rows);self.assertTrue(all(x['composed_status']=='OPEN' for x in rows))
 def test_missing_root_keeps_open(self):
  p=copy.deepcopy(self.p);del p['roots'][F];self.assert_open(p,self.r)
 def test_wrong_edge_prestate_keeps_open(self):
  p=copy.deepcopy(self.p);r=copy.deepcopy(self.r);k=F+' -> crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1';c=p['edges'][k];c['call_domain_certificate']['same_prestate']=False;c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r[k]=h;self.assert_open(p,r)
 def test_missing_late_child_keeps_open(self):
  p=copy.deepcopy(self.p);del p['members']['crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1'];self.assert_open(p,self.r)
if __name__=='__main__':unittest.main(verbosity=2)
