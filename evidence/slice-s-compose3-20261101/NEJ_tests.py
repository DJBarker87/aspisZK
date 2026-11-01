"""Mutation tests use real inherited certificates; no fabricated native credit."""
import copy,json,unittest
from unittest.mock import patch
import NEJ_validate as v
class CertificateMutations(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
  cls.packet=v.read(v.E/'NEJ_LEDGER_DELTA.json');cls.review=v.read(v.E/'NEJ_REVIEWED_CERTIFICATES.json')
  cls.f=next(f for f in cls.packet['members'] if f.endswith('::transfer_common'))
 def states(self,p,review=None):
  o=v.compose(self.base,p,self.review if review is None else review)
  return [r['composed_status'] for r in o['rows'] if r['function']==self.f]
 def test_inherited_leaf_remains_closed(self):self.assertEqual(set(self.states(self.packet)),{'CLOSED'})
 def test_missing_certificate_keeps_row_open(self):
  p=copy.deepcopy(self.packet);p['members'].pop(self.f)
  self.assertEqual(set(self.states(p)),{'OPEN'})
 def test_wrong_subject_keeps_row_open(self):
  p=copy.deepcopy(self.packet);p['members'][self.f]['subject']+=' wrong'
  self.assertEqual(set(self.states(p)),{'OPEN'})
 def test_missing_call_domain_is_not_a_new_certificate(self):
  p=copy.deepcopy(self.packet);p['members'][self.f]['id']='NEJ_unproved'
  self.assertEqual(set(self.states(p)),{'OPEN'})
 def test_nee_gate_is_necessary(self):
  with patch.object(v,'call_domain',return_value=True):self.assertFalse(v.certificate({},'x',self.base,{}))
 def test_new_gate_is_additional(self):
  with patch.object(v,'BASE_CERTIFICATE',return_value=True):self.assertFalse(v.certificate({'id':'NEJ_empty'},'x',self.base,{}))
 def test_wrong_domain_subject_rejected(self):self.assertFalse(v.call_domain({'call_domain_certificate':{'subject':'wrong'}},'edge',self.base))
 def test_missing_physical_proof_rejected(self):self.assertFalse(v.call_domain({'kind':'call-domain','call_domain_certificate':{'subject':'a -> b','frozen_revision':self.base['frozen_revision'],'native_association_kind':'ruling-y','domain_theorems':[],'physical_theorems':[]}},'a -> b',self.base))
 def test_changed_native_field_rejected(self):
  b=copy.deepcopy(self.base);b['rows'][0]['frozen_body_verified']=False
  with self.assertRaises(AssertionError):v.compose(b,self.packet,self.review)
 def test_validator_restored_after_failure(self):
  prior=v.predecessor.certificate
  with self.assertRaises(KeyError):v.compose({},self.packet,self.review)
  self.assertIs(v.predecessor.certificate,prior)
class RevalidatedMutations(CertificateMutations):
 @classmethod
 def setUpClass(cls):
  super().setUpClass()
  cls.f=next(f for f in cls.packet['members'] if f.endswith('M31::to_le_bytes'))
 def changed(self,edit):
  import hashlib
  p=copy.deepcopy(self.packet);c=p['members'][self.f];edit(c)
  c.pop('semantic_review_sha256',None)
  digest=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest()
  c['semantic_review_sha256']=digest;review=dict(self.review);review[self.f]=digest
  return self.states(p,review)
 def test_new_domain_binding_is_required(self):
  self.assertEqual(set(self.changed(lambda c:c.pop('call_domain_certificate'))),{'OPEN'})
 def test_wrong_domain_binding_even_if_reviewed_is_open(self):
  self.assertEqual(set(self.changed(lambda c:c['call_domain_certificate'].update(subject='wrong edge'))),{'OPEN'})
 def test_missing_physical_theorem_even_if_reviewed_is_open(self):
  self.assertEqual(set(self.changed(lambda c:c['call_domain_certificate'].update(physical_theorems=[]))),{'OPEN'})
 def test_missing_native_frame_even_if_reviewed_is_open(self):
  self.assertEqual(set(self.changed(lambda c:c['call_domain_certificate'].update(native_frame_complete=False))),{'OPEN'})
 def test_wrong_canonical_carrier_even_if_reviewed_is_open(self):
  self.assertEqual(set(self.changed(lambda c:c['call_domain_certificate'].update(canonical_carrier=False))),{'OPEN'})
 def test_missing_direct_native_contract_even_if_reviewed_is_open(self):
  self.assertEqual(set(self.changed(lambda c:c.pop('direct_contract'))),{'OPEN'})
class LoopCertificateMutations(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
  cls.packet=v.read(v.E/'NEJ_LEDGER_DELTA.json');cls.review=v.read(v.E/'NEJ_REVIEWED_CERTIFICATES.json')
  cls.f=next(f for f in cls.packet['members'] if 'pair_forest_accounts' in f and f.endswith('::digest_is_canonical'))
 def states(self,p,review=None):
  return {r['composed_status'] for r in v.compose(self.base,p,self.review if review is None else review)['rows'] if r['function']==self.f}
 def mutated(self,edit):
  import hashlib
  p=copy.deepcopy(self.packet);c=p['members'][self.f];edit(c['loop_composition'])
  c.pop('semantic_review_sha256',None);digest=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=digest
  review=dict(self.review);review[self.f]=digest
  return self.states(p,review)
 def test_complete_loop_closes(self):self.assertEqual(self.states(self.packet),{'CLOSED'})
 def test_missing_induction_keeps_loop_open(self):self.assertEqual(self.mutated(lambda q:q.pop('value_frame_theorem')),{'OPEN'})
 def test_old_existential_frame_does_not_replace_same_run_join(self):
  self.assertEqual(self.mutated(lambda q:q['value_frame_theorem'].update(name='NEE_CanonicalFrame.frame')),{'OPEN'})
 def test_missing_emitted_association_keeps_loop_open(self):self.assertEqual(self.mutated(lambda q:q.update(emitted_association_theorems=[])),{'OPEN'})
 def test_missing_control_keeps_loop_open(self):self.assertEqual(self.mutated(lambda q:q.pop('negative')),{'OPEN'})
 def test_wrong_native_frame_keeps_loop_open(self):self.assertEqual(self.mutated(lambda q:q.update(native_external_modifies=['input'])),{'OPEN'})
 def test_wrong_native_source_keeps_loop_open(self):self.assertEqual(self.mutated(lambda q:q.update(frozen_body_sha256='0'*64)),{'OPEN'})
 def test_missing_width_theorem_keeps_loop_open(self):self.assertEqual(self.mutated(lambda q:q.pop('external_length_theorem')),{'OPEN'})
 def test_missing_external_domain_keeps_loop_open(self):
  p=copy.deepcopy(self.packet);key=p['members'][self.f]['loop_composition']['external_ids'][0];p['externals'].pop(key)
  self.assertIn('OPEN',self.states(p))
 def test_wrong_loop_invariant_keeps_loop_open(self):self.assertEqual(self.mutated(lambda q:q.update(invariant='i<=9')),{'OPEN'})
if __name__=='__main__':unittest.main()
