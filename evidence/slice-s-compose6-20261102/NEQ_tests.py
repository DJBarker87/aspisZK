"""Actual unchanged NDT/NED fixed point must reject missing/wrong same-call certificates."""
import unittest,copy,hashlib,json
import NEQ_validate as v
from NEM_root_checks import F,CHILDREN
class Composition(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.b=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.p=v.read(v.E/'NEQ_LEDGER_DELTA.json');cls.r=v.read(v.E/'NEQ_REVIEWED_CERTIFICATES.json')
 def assert_open(self,p,r,f=F):
  out=v.compose(self.b,p,r);rows=[x for x in out['rows'] if x['function']==f]
  self.assertTrue(rows);self.assertTrue(all(x['composed_status']=='OPEN' for x in rows))
 def test_missing_root_certificate_keeps_rows_open(self):
  p=copy.deepcopy(self.p);del p['roots'][F];self.assert_open(p,self.r)
 def test_wrong_edge_certificate_keeps_root_open(self):
  p=copy.deepcopy(self.p);r=copy.deepcopy(self.r);key=F+' -> '+CHILDREN[-1];c=p['edges'][key];c['call_domain_certificate']['same_prestate']=False
  c.pop('semantic_review_sha256');h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;r[key]=h
  self.assert_open(p,r)
 def test_missing_child_member_keeps_parent_open(self):
  p=copy.deepcopy(self.p);del p['members'][CHILDREN[-1]];self.assert_open(p,self.r)
if __name__=='__main__':unittest.main(verbosity=2)
