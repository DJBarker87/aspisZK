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
if __name__=='__main__':unittest.main()
