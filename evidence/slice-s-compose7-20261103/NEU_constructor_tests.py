"""New bridge/domain mutations: no model-only or incomplete native promotion."""
import copy,json,hashlib,unittest
import NEU_validate as v
import NEU_bridge_checks as b
E=v.E
class Constructors(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
  cls.packet=v.read(E/'NEU_LEDGER_DELTA.json');cls.reviewed=v.read(E/'NEU_REVIEWED_CERTIFICATES.json')
  cls.f=b.P+'transfer_statement_box';cls.node=cls.packet['native_bridge_additions'][cls.f]
 @staticmethod
 def seal(node,reviewed,f):
  node.pop('semantic_review_sha256',None);node['semantic_review_sha256']=hashlib.sha256(json.dumps(node,sort_keys=True).encode()).hexdigest();reviewed['native-bridge::'+f]=node['semantic_review_sha256']
 def test_missing_field_window_rejected(self):
  node=copy.deepcopy(self.node);node['native_pairs'].pop();reviewed=dict(self.reviewed);self.seal(node,reviewed,self.f)
  self.assertFalse(b.addition(node,self.f,self.base,v,reviewed))
 def test_wrong_observed_field_rejected(self):
  node=copy.deepcopy(self.node);node['native_pairs'][0],node['native_pairs'][1]=node['native_pairs'][1],node['native_pairs'][0];reviewed=dict(self.reviewed);self.seal(node,reviewed,self.f)
  self.assertFalse(b.addition(node,self.f,self.base,v,reviewed))
 def test_stronger_domain_rejected(self):
  node=copy.deepcopy(self.node);node['domain']='only accepted canonical fixtures';reviewed=dict(self.reviewed);self.seal(node,reviewed,self.f)
  self.assertFalse(b.addition(node,self.f,self.base,v,reviewed))
 def test_wrong_model_theorem_rejected(self):
  node=copy.deepcopy(self.node);node['theorems'][2]=node['theorems'][0];reviewed=dict(self.reviewed);self.seal(node,reviewed,self.f)
  self.assertFalse(b.addition(node,self.f,self.base,v,reviewed))
 def test_no_native_control_no_credit(self):
  node=copy.deepcopy(self.node);node['native_pairs'][0][1]=node['native_pairs'][0][0];reviewed=dict(self.reviewed);self.seal(node,reviewed,self.f)
  self.assertFalse(b.addition(node,self.f,self.base,v,reviewed))
 def test_missing_call_certificate_keeps_row_open(self):
  packet=copy.deepcopy(self.packet);edge=next(e for e in packet['edges'] if e.startswith(self.f+' -> '));del packet['edges'][edge]
  out=v.compose(self.base,packet,self.reviewed)
  self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.f))
 def test_wrong_call_certificate_keeps_row_open(self):
  packet=copy.deepcopy(self.packet);reviewed=dict(self.reviewed);edge=next(e for e in packet['edges'] if e.startswith(self.f+' -> '));c=packet['edges'][edge];c['call_domain_certificate']['same_arguments']=False;c.pop('semantic_review_sha256');c['semantic_review_sha256']=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();reviewed[edge]=c['semantic_review_sha256']
  out=v.compose(self.base,packet,reviewed)
  self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.f))
 def test_missing_physical_certificate_keeps_row_open(self):
  packet=copy.deepcopy(self.packet);key=self.f+'::'+b.qualifiers(self.f)[1];del packet['hypotheses'][key]
  out=v.compose(self.base,packet,self.reviewed)
  self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.f))
 def test_missing_box_boundary_keeps_row_open(self):
  packet=copy.deepcopy(self.packet);key=next(k for k,c in packet['externals'].items() if c.get('native_bridge_function')==self.f);del packet['externals'][key]
  out=v.compose(self.base,packet,self.reviewed)
  self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.f))
if __name__=='__main__':unittest.main()
