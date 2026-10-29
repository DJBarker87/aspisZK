"""Required negative controls: absent/wrong certificates never grant closure."""
import copy,json,unittest
from unittest.mock import patch
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
 # These synthetic engine tests mock ONLY the certificate checker. They prove
 # overlay transitions/mutations, and provide no native or Lean evidence credit.
 def fixture(self):
  p=copy.deepcopy(self.packet)
  f='crates/aspis-core/src/field.rs::M31::from_le_bytes'
  rows=[r for r in self.base['rows'] if r['function']==f]
  self.assertTrue(rows and all(not r['canonical_callees'] and not r['open_transitive_dependencies'] for r in rows))
  p['members'][f]={'synthetic_token':'valid','id':'synthetic-engine-test'}
  for r in rows:
   for h in r['named_hypotheses']:p['hypotheses'][f+'::'+h['name']]={'synthetic_token':'valid','id':'synthetic-engine-test'}
   for o in r['caller_domain_obligations']:p['externals'][o['id']]={'synthetic_token':'valid','id':'synthetic-engine-test'}
  return p,rows
 def test_overlay_can_close_certified_leaf_synthetic(self):
  p,rows=self.fixture()
  def check(c,*args):return bool(c and c.get('synthetic_token')=='valid')
  with patch.object(v,'certificate',check):
   out=v.compose(self.base,p,{})
  self.assertEqual({r['row'] for r in out['rows'] if r['composed_status']=='CLOSED'},{r['row'] for r in rows})
  self.assertTrue(out['NED_composition_overlay']['native_statuses_unchanged'])
 def test_missing_hypothesis_keeps_leaf_open_synthetic(self):
  p,rows=self.fixture();p['hypotheses'].pop(next(iter(p['hypotheses'])))
  with patch.object(v,'certificate',lambda c,*args:bool(c and c.get('synthetic_token')=='valid')):
   self.assertEqual(self.closed(p),[])
 def test_wrong_certificate_keeps_leaf_open_synthetic(self):
  p,rows=self.fixture();p['members'][rows[0]['function']]['synthetic_token']='wrong'
  with patch.object(v,'certificate',lambda c,*args:bool(c and c.get('synthetic_token')=='valid')):
   self.assertEqual(self.closed(p),[])
if __name__=='__main__':unittest.main(verbosity=2)
