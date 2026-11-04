"""Missing, wrong and self-rehashed certificates keep the row OPEN."""
import unittest,copy,json
from unittest.mock import patch
import NEX_validate as v
from NEX_bridge_checks import EXACT,compose_additions
class Certificates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
  cls.packet=v.read(v.E/'NEX_LEDGER_DELTA.json');cls.reviewed=v.read(v.E/'NEX_REVIEWED_CERTIFICATES.json')
  # Reuse one baseline evaluation for mutations of the additional admission layer.
  P=v.E.parent/'slice-s-compose7-20261103'
  cls.baseline=v.inherited.compose(cls.base,v.read(P/'NEU_LEDGER_DELTA.json'),v.read(P/'NEU_REVIEWED_CERTIFICATES.json'))
  cls.external=next(o['id'] for r in cls.base['rows'] if r['function']==EXACT for o in r['caller_domain_obligations'])
 def rehash(self,p,c,subject):
  c['semantic_review_sha256']=v.sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  r=dict(self.reviewed);r[subject]=c['semantic_review_sha256'];return r
 def statuses(self,p,reviewed=None):
  out=compose_additions(self.base,self.baseline,p,reviewed or self.reviewed,v)
  return [r['composed_status'] for r in out['rows'] if r['function']==EXACT]
 def test_complete_packet(self):self.assertEqual(self.statuses(self.packet),['CLOSED','CLOSED'])
 def test_missing_member(self):
  p=copy.deepcopy(self.packet);del p['members'][EXACT];self.assertEqual(self.statuses(p),['OPEN','OPEN'])
 def test_missing_external_call_certificate(self):
  p=copy.deepcopy(self.packet);del p['externals'][self.external];self.assertEqual(self.statuses(p),['OPEN','OPEN'])
 def test_wrong_call_domain_rehashed(self):
  p=copy.deepcopy(self.packet);c=p['externals'][self.external];c['callee_domain_established']=False;r=self.rehash(p,c,self.external);self.assertEqual(self.statuses(p,r),['OPEN','OPEN'])
 def test_wrong_subject_rehashed(self):
  p=copy.deepcopy(self.packet);c=p['members'][EXACT];c['subject']='wrong caller -> wrong callee';r=self.rehash(p,c,EXACT);self.assertEqual(self.statuses(p,r),['OPEN','OPEN'])
 def test_wrong_native_width_rehashed(self):
  p=copy.deepcopy(self.packet);c=p['members'][EXACT];c['native_certificate']['domain']='all widths';r=self.rehash(p,c,EXACT);self.assertEqual(self.statuses(p,r),['OPEN','OPEN'])
 def test_missing_frame_rehashed(self):
  p=copy.deepcopy(self.packet);c=p['externals'][self.external];c['native_frame_complete']=False;r=self.rehash(p,c,self.external);self.assertEqual(self.statuses(p,r),['OPEN','OPEN'])
 def test_missing_axioms_theorem_rehashed(self):
  p=copy.deepcopy(self.packet);c=p['members'][EXACT];c['domain_theorems']=[];r=self.rehash(p,c,EXACT);self.assertEqual(self.statuses(p,r),['OPEN','OPEN'])
 def test_inherited_overlay_preserved(self):
  P=v.E.parent/'slice-s-compose7-20261103';old=v.read(P/'NEU_LEDGER_DELTA.json')
  for group in ['roots','members','edges','hypotheses','externals','inventory_edges']:
   actual={k:c for k,c in self.packet[group].items() if not c.get('id','').startswith('NEX_')}
   self.assertEqual(actual,old[group])
if __name__=='__main__':unittest.main()
