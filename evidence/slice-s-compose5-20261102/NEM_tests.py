"""Mutation tests for additional certificate gates; inherited suites are separate."""
import unittest,copy,json,hashlib
import NEM_validate as v
class Certificates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEM_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEM_REVIEWED_CERTIFICATES.json')
 def check_mutation(self,mutate):
  c=copy.deepcopy(self.p['members'][v.DIGEST]);mutate(c)
  c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h
  r=copy.deepcopy(self.r);r[v.DIGEST]=h
  self.assertFalse(v.certificate(c,v.DIGEST,self.b,r))
 def test_digest_accepted(self):self.assertTrue(v.certificate(self.p['members'][v.DIGEST],v.DIGEST,self.b,self.r))
 def test_missing(self):self.assertFalse(v.certificate(None,v.DIGEST,self.b,self.r))
 def test_wrong_count_invariant(self):self.check_mutation(lambda c:c['digest_composition'].update(invariant='count=0'))
 def test_no_native_pair(self):self.check_mutation(lambda c:c['digest_composition'].update(native_pairs=[]))
 def test_wrong_theorem(self):self.check_mutation(lambda c:c['digest_composition']['theorems'][0].update(name='NEM_DigestInstance.result_and_frame'))
 def test_wrong_source(self):self.check_mutation(lambda c:c['digest_composition'].update(frozen_body=''))
 def test_missing_frame(self):self.check_mutation(lambda c:c['call_domain_certificate'].update(native_frame_complete=False))
 def test_inner_domain(self):self.check_mutation(lambda c:c.update(inner_hypotheses_remaining=['Child.PacketDomain']))
 def test_wrong_arguments(self):self.check_mutation(lambda c:c['call_domain_certificate'].update(same_arguments=False))
 def test_extra_trust(self):self.check_mutation(lambda c:c['call_domain_certificate'].update(new_trust_rows=['NewTrust']))
if __name__=='__main__':unittest.main()
