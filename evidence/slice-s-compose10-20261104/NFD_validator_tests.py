"""Add-only certificate and source-correspondence rejection tests."""
import unittest,copy,json,subprocess
import NFD_validate as v
import NFD_source_checks as s
class SourceChecks(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.text=subprocess.check_output(['git','show',s.REV+':'+s.P],text=True)
 def test_exact_reference(self):self.assertTrue(s.request_reference(self.text)['exact_normalized_source'])
 def test_wrong_payment_window(self):
  t=self.text.replace('&bytes[REQUEST_PAYMENT_OFFSET..]','&bytes[REQUEST_PAYMENT_OFFSET+1..]',1)
  with self.assertRaises(AssertionError):s.request_reference(t)
 def test_wrong_reference_error(self):
  n='pub fn decode_pool_v1_pair_forest_terminal_request_reference_v1(';a=self.text.index(n)
  t=self.text[:a]+self.text[a:].replace('WrongMagic','WrongVersion',1)
  with self.assertRaises(AssertionError):s.request_reference(t)
 def test_wrong_reference_field(self):
  n='pub fn decode_pool_v1_pair_forest_terminal_request_reference_v1(';a=self.text.index(n)
  t=self.text[:a]+self.text[a:].replace('REQUEST_PROFILE_OFFSET..REQUEST_RELEASE_OFFSET','REQUEST_RELEASE_OFFSET..REQUEST_POOL_PROGRAM_OFFSET',1)
  with self.assertRaises(AssertionError):s.request_reference(t)
class Admission(unittest.TestCase):
 def test_missing_certificate(self):self.assertFalse(v.certificate(None,'root',{}))
 def test_wrong_certificate(self):self.assertFalse(v.certificate({'subject':'wrong'},'root',{}))
 def test_booleans_do_not_close(self):
  c=dict(subject='root',frozen_revision='f',inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification')
  for k in ['exact_callsite','canonical_carrier','same_arguments','same_prestate','same_result','same_ordered_effects','native_frame_complete','callee_domain_established']:c[k]=True
  c['semantic_review_sha256']=v.sha(json.dumps(c,sort_keys=True).encode())
  self.assertFalse(v.certificate(c,'root',{'frozen_revision':'f'}))
class CompleteRequest(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  import NFD_bridge_checks as b
  cls.f=b.REQUEST;cls.packet=v.read(v.E/'NFD_LEDGER_DELTA.json')
  cls.base=dict(rows=v.read(v.inherited.E/'NEY_CHECKED_ROWS.json'),frozen_revision=b.REV,trust_rows=[])
  cls.c=cls.packet['NFD_certificates'][cls.f]
 def mutated(self,fn):
  c=copy.deepcopy(self.c);fn(c);c['semantic_review_sha256']=v.sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode());return c
 def stays_open(self,c):
  out=v.compose(self.base,dict(inherits=self.packet['inherits'],NFD_certificates={} if c is None else {self.f:c}))
  self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.f))
 def test_positive_closes(self):
  self.assertTrue(v.certificate(self.c,self.f,self.base))
  out=v.compose(self.base,self.packet)
  self.assertTrue(all(r['composed_status']=='CLOSED' for r in out['rows'] if r['function']==self.f))
 def test_absent_stays_open(self):self.stays_open(None)
 def test_wrong_certificate_stays_open(self):
  c=self.mutated(lambda c:c.__setitem__('subject','other'));self.stays_open(c)
 def test_missing_edge_stays_open(self):
  c=self.mutated(lambda c:c['edges'].pop());self.stays_open(c)
 def test_wrong_callee_domain_stays_open(self):
  c=self.mutated(lambda c:next(iter(c['call_domain_certificates'].values())).__setitem__('callee_domain_established',False));self.stays_open(c)
 def test_missing_inner_name_discharge_stays_open(self):
  c=self.mutated(lambda c:next(iter(c['call_domain_certificates'].values())).__setitem__('inner_names_discharged',[]));self.stays_open(c)
 def test_wrong_Lean_theorem_stays_open(self):
  c=self.mutated(lambda c:c['domain_theorems'][0].__setitem__('name','NEX_PublicModel.result_state_effects'));self.stays_open(c)
 def test_missing_native_field_stays_open(self):
  c=self.mutated(lambda c:c['native_certificate']['pairs'].pop());self.stays_open(c)
 def test_wrong_native_field_stays_open(self):
  c=self.mutated(lambda c:c['native_certificate']['pairs'].__setitem__(0,c['native_certificate']['pairs'][1]));self.stays_open(c)
 def test_hidden_callee_hypothesis_stays_open(self):
  c=self.mutated(lambda c:c['inner_hypotheses_remaining'].append('callee.PacketDomain'));self.stays_open(c)
 def test_missing_receipt_stays_open(self):
  c=self.mutated(lambda c:c['support'].pop());self.stays_open(c)
 def test_extra_root_hypothesis_stays_open(self):
  c=self.mutated(lambda c:c['hypotheses'].append('child.PhysicalInterpretation'));self.stays_open(c)

if __name__=='__main__':unittest.main()
