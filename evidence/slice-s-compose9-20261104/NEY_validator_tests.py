"""Additive admission mutation tests; immutable predecessor checks stay active."""
import copy,json,unittest
import NEY_validate as v
import NEY_bridge_checks as b
class Admission(unittest.TestCase):
 def test_missing_certificate(self):
  self.assertFalse(v.certificate(None,b.TERMINAL,{'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'}))
 def test_wrong_subject(self):
  self.assertFalse(v.certificate({'subject':'other'},b.TERMINAL,{}))
 def test_missing_fields_cannot_promote(self):
  base={'rows':[dict(function=b.TERMINAL,composed_status='OPEN',bridge_status='OPEN',claim_ids=[],named_hypotheses=[],caller_domain_obligations=[],canonical_callees=[],open_transitive_dependencies=[])],'trust_rows':[]}
  packet={'NEY_certificates':{b.TERMINAL:{'subject':b.TERMINAL}}}
  out=b.compose_additions(base,copy.deepcopy(base),packet,v)
  self.assertEqual(out,base)
 def test_wrong_field_rejected(self):
  a='NEY_K001';m=v.read(v.E/(a+'-shape.json'))
  self.assertEqual(m['field_slot'],0)
  with self.assertRaises(AssertionError):b.attempt(a,1,'positive','terminal')
 def test_wrong_control_rejected(self):
  with self.assertRaises(AssertionError):b.attempt('NEY_K001',0,'value','terminal')
 def test_wrong_native_function_rejected(self):
  with self.assertRaises(AssertionError):b.check({'native_certificate':{'function':'unrelated'}},{})
class CompleteCertificate(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  p=v.read(v.E/'NEY_LEDGER_DELTA.json')
  if b.TERMINAL not in p.get('NEY_certificates',{}):raise unittest.SkipTest('complete terminal certificate not yet available')
  cls.cert=p['NEY_certificates'][b.TERMINAL]
  rows=json.loads((v.E/'NEY_CHECKED_ROWS.json').read_text())
  # The check binds each exact inventory id; status fields are irrelevant here.
  cls.base={'frozen_revision':cls.cert['frozen_revision'],'rows':rows}
 def mutated(self,edit):
  c=copy.deepcopy(self.cert);edit(c)
  c['semantic_review_sha256']=v.sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  return c
 def test_complete_accepted(self):
  self.assertTrue(v.certificate(self.cert,b.TERMINAL,self.base))
 def test_missing_edge_stays_open(self):
  c=self.mutated(lambda c:c['edges'].pop())
  self.assertFalse(v.certificate(c,b.TERMINAL,self.base))
 def test_wrong_inventory_obligation(self):
  c=self.mutated(lambda c:c['required_obligations'].__setitem__(0,'external:wrong'))
  self.assertFalse(v.certificate(c,b.TERMINAL,self.base))
 def test_missing_field_pair(self):
  c=self.mutated(lambda c:c['native_certificate']['pairs'].pop())
  self.assertFalse(v.certificate(c,b.TERMINAL,self.base))
 def test_wrong_field_certificate(self):
  c=self.mutated(lambda c:c['native_certificate']['pairs'].__setitem__(0,c['native_certificate']['pairs'][1]))
  self.assertFalse(v.certificate(c,b.TERMINAL,self.base))
 def test_inner_domain_cannot_hide(self):
  c=self.mutated(lambda c:c['inner_hypotheses_remaining'].append('callee.PacketDomain'))
  self.assertFalse(v.certificate(c,b.TERMINAL,self.base))
 def test_wrong_theorem(self):
  c=self.mutated(lambda c:c['domain_theorems'][0].__setitem__('name','NEX_PublicModel.result_state_effects'))
  self.assertFalse(v.certificate(c,b.TERMINAL,self.base))
 def test_same_arguments_required(self):
  c=self.mutated(lambda c:c.__setitem__('same_arguments',False))
  self.assertFalse(v.certificate(c,b.TERMINAL,self.base))
 def test_child_domain_not_root_hypothesis(self):
  c=self.mutated(lambda c:c['hypotheses'].append('callee.PacketDomain'))
  self.assertFalse(v.certificate(c,b.TERMINAL,self.base))
if __name__=='__main__':unittest.main()
