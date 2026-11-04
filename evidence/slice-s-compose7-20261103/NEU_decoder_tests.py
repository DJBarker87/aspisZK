"""Mutation tests for the216-byte helper packet and its same-call certificates."""
import copy,json,hashlib,unittest
import NEU_validate as v,NEU_bridge_checks as b
import NEU_decoder_checks as d
class DecodeHelpers(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');cls.packet=v.read(v.E/'NEU_LEDGER_DELTA.json');cls.reviewed=v.read(v.E/'NEU_REVIEWED_CERTIFICATES.json');cls.f=d.FUNCTIONS[0];cls.node=cls.packet['native_bridge_additions'][cls.f]
  historical=copy.deepcopy(cls.packet)
  for g in ['roots','members','edges','hypotheses','externals','inventory_edges']:historical[g]={k:c for k,c in historical[g].items() if not c.get('id','').startswith('NEU_')}
  # Historical baseline is immutable for every mutation below; all predecessor
  # checks execute here once. Only the additional admission layer is mutated.
  cls.historical=v.predecessor.compose(cls.base,historical,cls.reviewed)
 @staticmethod
 def seal(node,reviewed,f):
  node.pop('semantic_review_sha256',None);node['semantic_review_sha256']=hashlib.sha256(json.dumps(node,sort_keys=True).encode()).hexdigest();reviewed['native-bridge::'+f]=node['semantic_review_sha256']
 def rejected(self,alter):
  node=copy.deepcopy(self.node);reviewed=dict(self.reviewed);alter(node);self.seal(node,reviewed,self.f);self.assertFalse(d.addition(node,self.f,self.base,v,reviewed))
 def test_accepted_complete_packet(self):self.assertTrue(d.addition(self.node,self.f,self.base,v,self.reviewed))
 def test_missing_control(self):self.rejected(lambda n:n['native_pairs'][0].pop())
 def test_wrong_native_shape(self):self.rejected(lambda n:n.update(native_pairs=[['NEU_K124','NEU_K125']]))
 def test_stronger_domain(self):self.rejected(lambda n:n.update(domain='canonical successful bytes only'))
 def test_wrong_assembly(self):self.rejected(lambda n:n['theorems'].__setitem__(2,n['theorems'][0]))
 def test_missing_call_domain_open(self):
  packet=copy.deepcopy(self.packet);edge=next(e for e in packet['edges'] if e.startswith(self.f+' -> '));del packet['edges'][edge]
  out=b.compose(self.base,self.historical,packet,self.reviewed,v);self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.f))
 def test_wrong_call_domain_open(self):
  packet=copy.deepcopy(self.packet);reviewed=dict(self.reviewed);edge=next(e for e in packet['edges'] if e.startswith(self.f+' -> '));c=packet['edges'][edge];c['call_domain_certificate']['same_arguments']=False;c.pop('semantic_review_sha256');c['semantic_review_sha256']=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();reviewed[edge]=c['semantic_review_sha256']
  out=b.compose(self.base,self.historical,packet,reviewed,v);self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.f))
 def test_missing_physical_open(self):
  packet=copy.deepcopy(self.packet);del packet['hypotheses'][self.f+'::'+b.qualifiers(self.f)[1]]
  out=b.compose(self.base,self.historical,packet,self.reviewed,v);self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==self.f))
if __name__=='__main__':unittest.main()
