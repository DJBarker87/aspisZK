"""New fold-root intake denial tests; old NEI/NEO gates remain unchanged."""
import unittest,copy,json,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent
ALLOWED={'TX1:188','TX1:190','TX2:113','TX2:117'}
def check(packet):
 original=json.loads((E/'NET_PEER_POSITIVE.json').read_text())
 good={r['row']:r for r in original['rows'] if r['row'] in ALLOWED}
 goodcert={r['row']:r for r in original['row_certificates'] if r['row'] in ALLOWED}
 if set(packet)!= {'rows','row_certificates','revision'}:raise ValueError('packet shape')
 if packet['revision']!='5d12713bd3d7b813a911201357b22e2ef2d5acfa':raise ValueError('unreviewed revision')
 if len(packet['rows'])!=4 or {r['row']:r for r in packet['rows']}!=good:raise ValueError('unreviewed row or changed obligation')
 if len(packet['row_certificates'])!=4 or {r['row']:r for r in packet['row_certificates']}!=goodcert:raise ValueError('unreviewed recipe or changed proof')
 return True
class Gates(unittest.TestCase):
 def setUp(self):
  d=json.loads((E/'NET_PEER_POSITIVE.json').read_text());self.p={'revision':'5d12713bd3d7b813a911201357b22e2ef2d5acfa','rows':[r for r in d['rows'] if r['row'] in ALLOWED],'row_certificates':[r for r in d['row_certificates'] if r['row'] in ALLOWED]}
 def fail(self,f):
  p=copy.deepcopy(self.p);f(p)
  with self.assertRaises(ValueError):check(p)
 def test_positive(self):self.assertTrue(check(self.p))
 def test_revision(self):self.fail(lambda p:p.update(revision='35f682158d'))
 def test_missing_row(self):self.fail(lambda p:p['rows'].pop())
 def test_root_promotion(self):self.fail(lambda p:p['rows'][0].update(function='query_loop'))
 def test_native_recipe(self):self.fail(lambda p:p['row_certificates'][0].pop('native_review'))
 def test_missing_frame(self):self.fail(lambda p:p['row_certificates'][0]['parts'].remove('state'))
 def test_missing_order(self):self.fail(lambda p:p['row_certificates'][0]['parts'].remove('ordered_effects'))
 def test_hidden_hypothesis(self):self.fail(lambda p:p['row_certificates'][0]['remaining_inner_hypotheses'].append('callee'))
 def test_dropped_domain(self):self.fail(lambda p:p['row_certificates'][0]['named_hypotheses_discharged'].clear())
 def test_frozen_body(self):self.fail(lambda p:p['row_certificates'][0].update(frozen_body_sha256='0'*64))
 def test_missing_callee_proof(self):self.fail(lambda p:p['row_certificates'][0]['lean_evidence'].clear())
 def test_missing_external(self):self.fail(lambda p:next(c for c in p['row_certificates'] if c['external_obligations'])['external_obligations'].clear())
if __name__=='__main__':unittest.main()
