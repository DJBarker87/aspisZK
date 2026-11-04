import copy,json,unittest
from pathlib import Path
from unittest.mock import patch
import NFB_validate as v
import NFB_certificates as c
import NFB_root_source as source
import NFB_std_collect_checks as std
import NFB_caller_checks as callers
import NFB_external_checks as external
import NFB_proof_checks as proof
E=Path(__file__).resolve().parent
class Root(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.old=v.obj(v.O/'NEW_LEDGER_DELTA.json')
  cls.rows=v.obj(E/'NFB_CERTIFICATES.json');cls.edges=v.obj(E/'NFB_EDGES.json')
  cls.newrows,cls.replacements=c.expected(v.prior.net.neo.baseline())
 def validate(self,edges=None,rows=None):
  with patch.object(v.prior,'validate',return_value=copy.deepcopy(self.old)),patch.object(v,'expected',return_value=(copy.deepcopy(self.newrows),copy.deepcopy(self.replacements))):
   return v.validate(edges=copy.deepcopy(self.edges) if edges is None else edges,certificates=copy.deepcopy(self.rows) if rows is None else rows,replay=False)
 def test_positive(self):
  r=self.validate();self.assertEqual(r['q_functions_closed'],64);self.assertEqual(r['q_occurrences_closed'],128)
  self.assertEqual(r['roots'][c.ROOT],'CLOSED');self.assertFalse(r['security_target_established'])
 def test_query_loop_open(self):self.assertEqual(self.validate()['roots']['crates/aspis-r1-cost-probe/src/candidate.rs::query_loop'],'OPEN')
 def test_inner_bridge(self):
  rows=copy.deepcopy(self.rows);rows[0]['remaining_inner_hypotheses']=['ChildBridge']
  with self.assertRaises(AssertionError):self.validate(rows=rows)
 def test_missing_row(self):
  with self.assertRaises(AssertionError):self.validate(rows=self.rows[:1])
 def test_wrong_domain(self):
  rows=copy.deepcopy(self.rows);rows[0]['domain']='honest fixtures only'
  with self.assertRaises(AssertionError):self.validate(rows=rows)
 def test_omit_external(self):
  rows=copy.deepcopy(self.rows);rows[0]['external_obligations'].popitem()
  with self.assertRaises(AssertionError):self.validate(rows=rows)
 def test_change_inventory_domain(self):
  rows=copy.deepcopy(self.rows);rows[0]['inventory_obligations'][0]['status']='OPEN'
  with self.assertRaises(AssertionError):self.validate(rows=rows)
 def test_changed_root_body(self):
  rows=copy.deepcopy(self.rows);rows[0]['frozen_body_sha256']='0'*64
  with self.assertRaises(AssertionError):self.validate(rows=rows)
 def test_missing_edge(self):
  edges=copy.deepcopy(self.edges);edges['edges'].pop()
  with self.assertRaises(AssertionError):self.validate(edges=edges)
 def test_incoming_not_inferred(self):
  edges=copy.deepcopy(self.edges)
  edge=next(e for e in edges['edges'] if e['caller'].endswith('::query_loop') and e['status']=='OPEN')
  edge['status']='CLOSED'
  with self.assertRaises(AssertionError):self.validate(edges=edges)
 def test_prune_real_target(self):
  edges=copy.deepcopy(self.edges)
  edge=next(e for e in edges['edges'] if e['caller']==c.ROOT and e['callee'].endswith('::M31::mul'))
  edge['selected_target']=False
  with self.assertRaises(AssertionError):self.validate(edges=edges)
 def test_unknown_external(self):
  with self.assertRaises(AssertionError):external.law({'syntax':'arbitrary_runtime_hook'})
class Concrete(unittest.TestCase):
 def test_source(self):self.assertEqual(source.check()['root'],c.ROOT)
 def test_wrong_root_call(self):
  from NFB_source_checks import frozen
  text=frozen().replace('suffix_inverse.mul(prefixes[i])','suffix_inverse.mul(flat[i])')
  with self.assertRaises(AssertionError):source.check(release=text)
 def test_wrong_guard(self):
  candidate=callers.frozen('crates/aspis-r1-cost-probe/src/candidate.rs')
  with self.assertRaises((AssertionError,StopIteration)):callers.check(candidate=candidate.replace('if k != SPLIT','if k == SPLIT'))
 def test_wrong_split(self):
  compact=callers.frozen('crates/aspis-r1-cost-probe/src/compact.rs')
  with self.assertRaises(AssertionError):callers.check(compact=compact.replace('SPLIT: usize = 10','SPLIT: usize = 11'))
 def test_std_store(self):
  native=(E/'NFB_geometry.rs.txt').read_text()
  with self.assertRaises(AssertionError):std.check(source=native.replace('ptr.add(*local_len),element','ptr.add(0),element'))
 def test_std_counter(self):
  texts={n:(E/('NFB_STD_'+n+'.rs.txt')).read_text() for n in std.FILES}
  texts['alloc_vec_set_len_on_drop']=texts['alloc_vec_set_len_on_drop'].replace('*self.len = self.local_len;','*self.len = 0;')
  with self.assertRaises(AssertionError):std.check(texts)
 def test_nonstandard_axiom(self):
  original=proof.obj
  def mutated(path):
   d=original(path)
   if str(path).endswith('NFB_L070/receipt.json'):d['print_axioms']=["'NFB_GeometryComposed.result_state_effects' depends on axioms: [HiddenBridge]"]
   return d
  with patch.object(proof,'obj',side_effect=mutated),self.assertRaises(AssertionError):proof.accepted('NFB_GeometryComposed')
if __name__=='__main__':unittest.main()
