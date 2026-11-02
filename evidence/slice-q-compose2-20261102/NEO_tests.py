"""Mutation tests on actual baseline and replayed certificates; no fake credit."""
import unittest,copy,json,time
from unittest.mock import patch
import NEO_validate as v
class Gates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.base=v.baseline();cls.peer=v.obj(v.E/'NEO_PEER_POSITIVE.json');cls.edges=v.obj(v.E/'NEO_EDGES.json');cls.data=v.peer_inputs()
 def run_case(self,base=None,peer=None,edges=None):
  with patch.object(v,'peer_inputs',return_value=self.data):
   return v.compose(self.base if base is None else base,self.peer if peer is None else peer,self.edges if edges is None else edges)
 def test_positive(self):
  d=self.run_case();self.assertEqual((d['total_closed'],d['q_closed'],d['edge_closed']),(92,70,108));self.assertEqual(set(d['roots'].values()),{'OPEN'})
 def test_baseline_suspension_cannot_be_cleared(self):
  b=copy.deepcopy(self.base);next(c for c in b['NEN_credits'] if c['k3_status']=='SUSPENDED')['k3_status']='UNAFFECTED'
  with self.assertRaises(ValueError):self.run_case(base=b)
 def test_historical_quarantine_cannot_be_removed(self):
  b=copy.deepcopy(self.base);b['quarantine']=[]
  with self.assertRaises(ValueError):self.run_case(base=b)
 def test_root_cannot_be_promoted(self):
  p=copy.deepcopy(self.peer);p['rows'][0]['function']=next(iter(v.ROOTS))
  with self.assertRaises(ValueError):self.run_case(peer=p)
 def test_missing_peer_row(self):
  p=copy.deepcopy(self.peer);p['rows'].pop()
  with self.assertRaises(ValueError):self.run_case(peer=p)
 def test_changed_inner_hypothesis(self):
  p=copy.deepcopy(self.peer);p['rows'][0]['named_hypotheses'][0]['discharged_by']=None
  with self.assertRaises(ValueError):self.run_case(peer=p)
 def test_missing_native_association(self):
  p=copy.deepcopy(self.peer);p['row_certificates'][0]['parts'].remove('native_association')
  with self.assertRaises(ValueError):self.run_case(peer=p)
 def test_changed_result_recipe(self):
  p=copy.deepcopy(self.peer);p['row_certificates'][0]['parts'].remove('result')
  with self.assertRaises(ValueError):self.run_case(peer=p)
 def test_unregistered_edge(self):
  e=copy.deepcopy(self.edges);e['edges'][0]['certificate']=None
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_missing_constructor_edge(self):
  e=copy.deepcopy(self.edges);name=self.peer['edges'][0]['edge'];next(x for x in e['edges'] if x['edge']==name)['certificate']=None
  with self.assertRaises(ValueError):self.run_case(edges=e)
 def test_wrong_occurrence(self):
  p=copy.deepcopy(self.peer)
  c=next(c for c in p['row_certificates'] if c['row']=='TX2:073');next(iter(c['external_obligations'].values()))['ordinal']=99
  with self.assertRaises(ValueError):self.run_case(peer=p)
 def test_edge_inventory_retained(self):
  e=copy.deepcopy(self.edges);e['edges'].pop()
  with self.assertRaises(ValueError):self.run_case(edges=e)
if __name__=='__main__':
 start=time.monotonic();suite=unittest.defaultTestLoader.loadTestsFromTestCase(Gates);result=unittest.TextTestRunner(verbosity=2).run(suite)
 receipt=dict(target='NEO_tests.py',tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),exit_status=0 if result.wasSuccessful() else 1,wall_seconds=time.monotonic()-start,peak_aggregate_rss_bytes_sampled=v.nen.PEAK_AGGREGATE_RSS,swap='not measured: Python evidence validation',print_axioms='N/A: preserved printed proof audits checked in replay')
 (v.E/'NEO_TESTS_RECEIPT.json').write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(receipt));raise SystemExit(receipt['exit_status'])
