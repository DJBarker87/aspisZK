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
  out=v.compose(self.base,self.packet,self.review);self.assertEqual(len(v.predecessor.summary(out)['slice_closed']),22)
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

class CommonMutations(Mutations):
 def common_status(self,p,review=None):
  o=v.compose(self.base,p,self.review if review is None else review)
  return {r['composed_status'] for r in o['rows'] if r['function']==v.COMMON}
 def test_missing_common_edge(self):
  p=copy.deepcopy(self.packet);p['edges'].pop(v.COMMON+' -> '+v.CANONICAL);self.assertEqual(self.common_status(p),{'OPEN'})
 def test_missing_common_constructor(self):
  p=copy.deepcopy(self.packet);p['externals'].pop('external:TX1:298:1');self.assertIn('OPEN',self.common_status(p))
 def test_scalar_control_missing_after_review(self):
  p=copy.deepcopy(self.packet);c=p['members'][v.COMMON];c['framed_scalar_caller']['controls'].pop('frame');c.pop('semantic_review_sha256');h=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review=dict(self.review,**{v.COMMON:h});self.assertEqual(self.common_status(p,review),{'OPEN'})
 def test_scalar_guard_stronger_domain_rejected(self):
  p=copy.deepcopy(self.packet);c=p['members'][v.COMMON];c['framed_scalar_caller']['all_typed_inputs']=False;c.pop('semantic_review_sha256');h=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review=dict(self.review,**{v.COMMON:h});self.assertEqual(self.common_status(p,review),{'OPEN'})
 def test_scalar_wrong_substitution_after_review(self):
  p=copy.deepcopy(self.packet);c=p['members'][v.COMMON];c['framed_scalar_caller']['model_theorems'][0]['name']='wrong';c.pop('semantic_review_sha256');h=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review=dict(self.review,**{v.COMMON:h});self.assertEqual(self.common_status(p,review),{'OPEN'})


class PaymentMutations(Mutations):
 def payment_status(self,p,review=None):
  out=v.compose(self.base,p,self.review if review is None else review)
  return {r['composed_status'] for r in out['rows'] if r['function'].endswith('::validate_pool_v1_private_transfer_public_v1')}
 def test_payment_missing_field_identity(self):
  p=copy.deepcopy(self.packet);f=next(f for f in p['members'] if f.endswith('::validate_pool_v1_private_transfer_public_v1'));c=p['members'][f];c['payment_caller']['theorems'].pop();c.pop('semantic_review_sha256');h=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review=dict(self.review,**{f:h});self.assertEqual(self.payment_status(p,review),{'OPEN'})
 def test_payment_missing_common_domain(self):
  p=copy.deepcopy(self.packet);p['members'].pop(v.COMMON);self.assertEqual(self.payment_status(p),{'OPEN'})
 def test_common_needs_corrupted_reply_control(self):
  p=copy.deepcopy(self.packet);c=p['members'][v.COMMON];c['framed_scalar_caller'].pop('corrupted_reply_control');c.pop('semantic_review_sha256');h=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review=dict(self.review,**{v.COMMON:h});o=v.compose(self.base,p,review);self.assertIn('OPEN',{r['composed_status'] for r in o['rows'] if r['function']==v.COMMON})
 def test_false_receiver_alternative_rejected_after_review(self):
  p=copy.deepcopy(self.packet);key=next(k for k,c in p['edges'].items() if 'receiver_resolution' in c);c=p['edges'][key];c['receiver_resolution']['receiver']='&WideExact';c.pop('semantic_review_sha256');h=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review=dict(self.review,**{key:h});self.assertFalse(v.certificate(c,key,self.base,review))

if __name__=='__main__':unittest.main()
