"""Mutations preserve OPEN for absent or wrong same-call certificates."""
import unittest,copy,json,hashlib
from pathlib import Path
import NEU_validate as v
class Certificates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
  cls.packet=v.read(v.E.parent/'slice-s-compose6-20261102/NEQ_LEDGER_DELTA.json')
  cls.reviewed=v.read(v.E.parent/'slice-s-compose6-20261102/NEQ_REVIEWED_CERTIFICATES.json')
  cls.function='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1'
  cls.edge=next(e for e,c in cls.packet['edges'].items() if e.startswith(cls.function+' -> ') and c.get('id','').startswith('NEQ_') and c['kind']=='call-domain')
 def test_missing_certificate(self):
  self.assertFalse(v.certificate(None,self.edge,self.base,self.reviewed))
 def test_wrong_domain_even_if_review_hash_refreshed(self):
  c=copy.deepcopy(self.packet['edges'][self.edge]);c['call_domain_certificate']['subject']='wrong caller -> wrong callee'
  c['semantic_review_sha256']=hashlib.sha256(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode()).hexdigest()
  r=dict(self.reviewed);r[self.edge]=c['semantic_review_sha256']
  self.assertFalse(v.certificate(c,self.edge,self.base,r))
 def test_incomplete_frame_even_if_review_hash_refreshed(self):
  c=copy.deepcopy(self.packet['edges'][self.edge]);c['call_domain_certificate']['native_frame_complete']=False
  c['semantic_review_sha256']=hashlib.sha256(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode()).hexdigest()
  r=dict(self.reviewed);r[self.edge]=c['semantic_review_sha256']
  self.assertFalse(v.certificate(c,self.edge,self.base,r))
 def test_missing_certificate_keeps_row_open(self):
  p=copy.deepcopy(self.packet);del p['edges'][self.edge]
  out=v.compose(self.base,p,self.reviewed)
  self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.function))
 def test_wrong_certificate_keeps_row_open(self):
  p=copy.deepcopy(self.packet);p['edges'][self.edge]['call_domain_certificate']['same_arguments']=False
  out=v.compose(self.base,p,self.reviewed)
  self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.function))
if __name__=='__main__':unittest.main()
