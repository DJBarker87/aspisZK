"""New bridge and internal-edge mutations; preserve all inherited checks."""
import unittest,copy,json,functools
import NEX_validate as v
import NEX_new_bridges as n
from NEX_bridge_checks import compose_additions
class NewCertificates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
  cls.packet=v.read(v.E/'NEX_LEDGER_DELTA.json');cls.reviewed=v.read(v.E/'NEX_REVIEWED_CERTIFICATES.json')
  P=v.E.parent/'slice-s-compose7-20261103'
  inherited=v.inherited.compose(cls.base,v.read(P/'NEU_LEDGER_DELTA.json'),v.read(P/'NEU_REVIEWED_CERTIFICATES.json'))
  cls.original_native=v.native;v.native=functools.lru_cache(None)(v.native)
  no_new=copy.deepcopy(cls.packet);no_new['NEX_new_bridges']={}
  cls.before=compose_additions(cls.base,inherited,no_new,cls.reviewed,v)
  cls.target=n.FUNCTIONS['lane']
  cls.edge=next(s for s in cls.packet['edges'] if s.startswith(cls.target+' -> '))
 @classmethod
 def tearDownClass(cls):v.native=cls.original_native
 def rehash(self,c,r,subject):
  c['semantic_review_sha256']=v.sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode());r[subject]=c['semantic_review_sha256']
 def status(self,p,r=None):
  x=n.compose(self.base,self.before,p,r or self.reviewed,v)
  return [a['composed_status'] for a in x['rows'] if a['function']==self.target]
 def test_complete_new_bridge(self):self.assertTrue(all(x=='CLOSED' for x in self.status(self.packet)))
 def test_missing_internal_edge(self):
  p=copy.deepcopy(self.packet);del p['edges'][self.edge];self.assertTrue(all(x=='OPEN' for x in self.status(p)))
 def test_wrong_internal_domain_self_rehashed(self):
  p=copy.deepcopy(self.packet);r=dict(self.reviewed);c=p['edges'][self.edge];c['callee_domain_established']=False;self.rehash(c,r,self.edge);self.assertTrue(all(x=='OPEN' for x in self.status(p,r)))
 def test_missing_new_child_names_self_rehashed(self):
  p=copy.deepcopy(self.packet);r=dict(self.reviewed);c=p['edges'][self.edge]
  c['required_named_hypotheses']=[];c['call_domain_certificate']['inner_names_discharged']=[]
  self.rehash(c,r,self.edge);self.assertTrue(all(x=='OPEN' for x in self.status(p,r)))
 def test_missing_parent_qualification(self):
  p=copy.deepcopy(self.packet);del p['hypotheses'][self.target+'::'+n.qualifiers(self.target)[0]]
  self.assertTrue(all(x=='OPEN' for x in self.status(p)))
if __name__=='__main__':unittest.main()
