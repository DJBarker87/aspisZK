import unittest,copy,json
import NFJ_validate as v
import NFH_validator_tests as prior
class Scanner(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.packet=v.read(v.E/'NFJ_LEDGER_DELTA.json');cls.c=cls.packet['NFJ_certificates'][v.F]
  cls.base=dict(rows=v.read(v.E/'NFJ_BASELINE_ROWS.json'),frozen_revision=v.REV,trust_rows=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')['trust_rows'])
 def mutate(self,fn):
  c=copy.deepcopy(self.c);fn(c);c['semantic_review_sha256']=v.sha(json.dumps({k:w for k,w in c.items() if k!='semantic_review_sha256'},sort_keys=True).encode());return c
 def rejects(self,fn):self.assertFalse(v.certificate(self.mutate(fn),self.base))
 def test_positive(self):self.assertTrue(v.certificate(self.c,self.base))
 def test_no_certificate_stays_open(self):
  out=v.compose(self.base,dict(inherits=self.packet['inherits'],NFJ_certificates={}))
  self.assertEqual(out,self.base)
 def test_rehashed_flags(self):
  for flag in v.FLAGS:
   with self.subTest(flag=flag):self.rejects(lambda c:c.update({flag:False}))
 def test_runtime_named_and_added(self):
  for key,val in [('new_trust_rows',[]),('runtime_contract','universal memcmp'),('hypotheses',v.HYPOTHESES[:-1]),('trust_classification','trust removed')]:
   with self.subTest(key=key):self.rejects(lambda c:c.update({key:val}))
 def test_lengths_and_same_places(self):
  for key in ['left','right','left_length','right_length','length_argument','reply','observation','completion','equal_continuation','unequal_continuation']:
   with self.subTest(key=key):self.rejects(lambda c:c['runtime_domain'].update({key:'wrong'}))
 def test_other_slot_observer(self):self.rejects(lambda c:c['runtime_domain'].update(other_slot_observers=['sign']))
 def test_no_inner_premise(self):self.rejects(lambda c:c.update(inner_hypotheses_remaining=['nativeEqualityBridge']))
 def test_missing_edge(self):self.rejects(lambda c:c['call_domain_certificates'].pop(c['edges'][0]))
 def test_edge_domain(self):self.rejects(lambda c:next(iter(c['call_domain_certificates'].values())).update(classification='canonical inputs only'))
 def test_edge_inner_names(self):self.rejects(lambda c:next(iter(c['call_domain_certificates'].values())).update(inner_names_discharged=[]))
 def test_edge_argument(self):self.rejects(lambda c:next(iter(c['call_domain_certificates'].values())).update(same_arguments=False))
 def test_edge_claim(self):self.rejects(lambda c:next(iter(c['call_domain_certificates'].values())).update(selected_callee_claims=[]))
 def test_missing_primitive(self):self.rejects(lambda c:c['primitive_certificates'].pop('external:TX2:226:9'))
 def test_wrong_primitive(self):self.rejects(lambda c:c['primitive_certificates'].update({'external:TX2:226:9':'trusted equality on arbitrary buffers'}))
 def test_missing_completion_theorem(self):self.rejects(lambda c:c['domain_theorems'].pop(2))
 def test_wrong_theorem_statement(self):self.rejects(lambda c:c['domain_theorems'][0].update(statement='True'))
 def test_missing_native_control(self):self.rejects(lambda c:c['native_certificate']['controls'].pop())
 def test_wrong_native_domain(self):self.rejects(lambda c:c['native_certificate'].update(domain='canonical contents only'))
 def test_missing_support(self):self.rejects(lambda c:c['support'].pop())
 def test_corrupt_support(self):self.rejects(lambda c:c['support'][0].update(sha256='0'*64))
 def test_source_mutation(self):
  from NFJ_source_checks import frozen_body,review
  with self.assertRaises(AssertionError):review(frozen_body().replace('!= candidate_bytes','== candidate_bytes'))
 def test_full_result(self):
  out=v.compose(self.base,self.packet);row=next(r for r in out['rows'] if r['function']==v.F)
  self.assertEqual(row['composed_status'],'CLOSED');self.assertTrue(all(o['status']=='CLOSED' for o in row['caller_domain_obligations']))
  self.assertEqual(out['trust_rows'][-1],v.TRUST);self.assertEqual(row['open_transitive_dependencies'],[])
 def test_unrelated_rows_identical(self):
  out=v.compose(self.base,self.packet)
  self.assertEqual([r for r in out['rows'] if r['function']!=v.F],[r for r in self.base['rows'] if r['function']!=v.F])
 def test_open_callee_blocks(self):
  b=copy.deepcopy(self.base);next(r for r in b['rows'] if r['function']==next(iter(v.CLASSIFICATIONS)))['composed_status']='OPEN'
  self.assertFalse(v.certificate(self.c,b))
def load_tests(loader,tests,pattern):
 tests.addTests(loader.loadTestsFromModule(prior));return tests
if __name__=='__main__':unittest.main()
