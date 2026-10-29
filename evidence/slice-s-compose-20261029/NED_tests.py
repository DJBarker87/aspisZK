"""Required negative controls: absent/wrong certificates never grant closure."""
import copy,json,unittest
from pathlib import Path
import NED_validate as v
E=Path(__file__).resolve().parent
class CertificateControls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.packet=v.read(E/'NED_LEDGER_DELTA.json')
 def closed(self,p,reviewed=None):return [r['row'] for r in v.compose(self.base,p,reviewed or {})['rows'] if r['composed_status']=='CLOSED']
 def test_missing_certificates(self):self.assertEqual(self.closed(self.packet),[])
 def test_wrong_edge_certificate(self):
  p=copy.deepcopy(self.packet);edge=v.read(E/'NED_EDGES.json')['edges'][0]['edge'];p['edges'][edge]={'kind':'call-domain','subject':edge+'wrong','frozen_revision':self.base['frozen_revision']};self.assertEqual(self.closed(p),[])
 def test_unreviewed_certificate(self):
  p=copy.deepcopy(self.packet);root=v.read(E/'NED_SCOPE.json')['slice']['roots'][1];p['roots'][root]={'kind':'root-composition','subject':root,'frozen_revision':self.base['frozen_revision'],'semantic_review_sha256':'0'*64};self.assertEqual(self.closed(p),[])
 def test_model_only_is_ineligible(self):self.assertFalse(v.certificate({'kind':'model-only'},'x',self.base,{}))
 def test_wrong_frozen_revision(self):
  p=copy.deepcopy(self.packet);p['frozen_revision']='0'*40
  with self.assertRaises(AssertionError):self.closed(p)
 def test_changed_baseline(self):
  p=copy.deepcopy(self.packet);p['base_sha256']='0'*64
  with self.assertRaises(AssertionError):self.closed(p)
 def test_outside_slice_edge(self):
  p=copy.deepcopy(self.packet);p['edges']['foreign -> foreign']={}
  with self.assertRaises(AssertionError):self.closed(p)
 def test_inherited_invariants_still_run(self):
  b=copy.deepcopy(self.base);b['rows'][0]['frozen_body_verified']=False
  with self.assertRaises(AssertionError):v.compose(b,self.packet,{})
 def test_missing_axioms_cannot_pass(self):self.assertFalse(v.certificate({'kind':'call-domain','subject':'x','frozen_revision':self.base['frozen_revision'],'theorems':[]},'x',self.base,{}))
if __name__=='__main__':unittest.main(verbosity=2)
