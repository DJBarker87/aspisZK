import unittest,copy,json
from unittest.mock import patch
import NEL_validate as v
class Mutations(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.packet=v.read(v.E/'NEL_LEDGER_DELTA.json');cls.review=v.read(v.E/'NEL_REVIEWED_CERTIFICATES.json');cls.f=v.GETTER
 def status(self,p,review=None):
  o=v.compose(self.base,p,self.review if review is None else review)
  return {r['composed_status'] for r in o['rows'] if r['function']==self.f}
 def test_inherited_fourteen_and_getter(self):
  out=v.compose(self.base,self.packet,self.review);self.assertEqual(len(v.predecessor.summary(out)['slice_closed']),16)
 def test_missing_member(self):
  p=copy.deepcopy(self.packet);p['members'].pop(self.f);self.assertEqual(self.status(p),{'OPEN'})
 def test_wrong_subject(self):
  p=copy.deepcopy(self.packet);p['members'][self.f]['subject']='wrong';self.assertEqual(self.status(p),{'OPEN'})
 def test_missing_domain_certificate(self):
  p=copy.deepcopy(self.packet);p['members'][self.f].pop('call_domain_certificate');self.assertEqual(self.status(p),{'OPEN'})
 def test_missing_named_domain(self):
  p=copy.deepcopy(self.packet);p['hypotheses'].pop(next(k for k in p['hypotheses'] if k.startswith(self.f+'::')));self.assertEqual(self.status(p),{'OPEN'})
 def test_missing_borrow_proof(self):
  p=copy.deepcopy(self.packet);p['members'][self.f].pop('borrowed_projection');self.assertEqual(self.status(p),{'OPEN'})
 def test_invalid_native_pair(self):
  with patch.object(v,'native_pair',return_value=False):self.assertEqual(self.status(self.packet),{'OPEN'})
 def test_never_relax_inherited_gate(self):
  with patch.object(v.predecessor.predecessor,'BASE_CERTIFICATE',return_value=False):self.assertFalse(v.certificate(self.packet['members'][self.f],self.f,self.base,self.review))
 def test_source_mutation_even_after_review(self):
  p=copy.deepcopy(self.packet);c=p['members'][self.f];c['borrowed_projection']['extracted_identity']='wrong';c.pop('semantic_review_sha256');h=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review=dict(self.review,**{self.f:h});self.assertEqual(self.status(p,review),{'OPEN'})
 def test_wrong_certificate_after_review(self):
  p=copy.deepcopy(self.packet);c=p['members'][self.f];c['call_domain_certificate']['native_frame_complete']=False;c.pop('semantic_review_sha256');h=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review=dict(self.review,**{self.f:h});self.assertEqual(self.status(p,review),{'OPEN'})
if __name__=='__main__':unittest.main()
