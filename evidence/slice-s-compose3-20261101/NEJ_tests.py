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
if __name__=='__main__':unittest.main()
