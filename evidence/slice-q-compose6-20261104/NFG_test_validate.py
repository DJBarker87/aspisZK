"""Mutation checks for additive rows, root packets, native controls and source cuts."""
import copy,json,unittest
from pathlib import Path
import NFG_validate as v
import NFG_native_checks as n
from NFG_chain_source import check as chain
from NFG_proof_checks import accepted
E=Path(__file__).resolve().parent
class RootTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.rows,cls.edges,cls.new=v.canonical()
  cls.delta=v.obj(E/'NFG_LEDGER_DELTA.json')
 def rejects(self,edges=None,rows=None):
  with self.assertRaises(AssertionError):v.validate(edges=edges,certificates=rows)
 def test_positive(self):self.assertEqual(v.validate(),self.delta)
 def test_extra_root(self):
  r=copy.deepcopy(self.rows);r.append(dict(row='TX1:181',function='query_loop'));self.rejects(rows=r)
 def test_missing_row(self):self.rejects(rows=self.rows[:-1])
 def test_inner_hypothesis(self):
  r=copy.deepcopy(self.rows);r[0]['remaining_inner_hypotheses']=['callee_reply'];self.rejects(rows=r)
 def test_weaker_domain(self):
  r=copy.deepcopy(self.rows);r[0]['domain']='all raw words';self.rejects(rows=r)
 def test_stronger_domain(self):
  r=copy.deepcopy(self.rows);r[0]['domain']+=' and selected successful child';self.rejects(rows=r)
 def test_pruned_edge(self):
  e=copy.deepcopy(self.edges);e['edges'].pop();self.rejects(edges=e)
 def test_four_dot_promotion(self):
  e=copy.deepcopy(self.edges);t=next(x for x in e['edges'] if 'four_dots_one' in x['caller'] and x['status']=='OPEN');t['status']='CLOSED';self.rejects(edges=e)
 def test_fake_callsite(self):
  e=copy.deepcopy(self.edges);t=next(x for x in e['edges'] if x['edge'] in self.new);t['certificate']['residual_inner_hypotheses']=['physical'];self.rejects(edges=e)
 def test_verifier_native_window(self):
  self.assertEqual(n.one('NFG_K041',0)['target'],'verifier::NFG_inverse::qm_neg')
 def test_verifier_feature_flags(self):
  r=json.loads((E/'NFG_K041/receipt.json').read_text());c=r['native_command'];c[c.index('--features')+1]='r0'
  with self.assertRaises(AssertionError):n.one('NFG_K041',0,r)
 def test_raw_program_coupling(self):
  p=v.obj(E/'NFG_PACKETS.json');self.assertIn('NFF_LoggedRaw.headline',p['raw_coupling']['model']);self.assertEqual(p['raw_coupling']['residual_inner_hypotheses'],[])
  self.assertNotIn('crates/aspis-core/src/field.rs::QM31::neg',p['roots'])
 def test_scope_caps(self):
  r=json.loads((E/'NFG_K021/receipt.json').read_text());r['limits']['memory.max']='17179869184'
  with self.assertRaises(AssertionError):n.one('NFG_K021',0,r)
 def test_native_verdict(self):
  r=json.loads((E/'NFG_K021/receipt.json').read_text());r['exit_status']=124
  with self.assertRaises(AssertionError):n.one('NFG_K021',0,r)
 def test_offline_required(self):
  r=json.loads((E/'NFG_K021/receipt.json').read_text());r['env']['CARGO_NET_OFFLINE']='false'
  with self.assertRaises(AssertionError):n.one('NFG_K021',0,r)
 def test_optimized_required(self):
  r=json.loads((E/'NFG_K021/receipt.json').read_text());r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']='0'
  with self.assertRaises(AssertionError):n.one('NFG_K021',0,r)
 def test_copy_patch_required(self):
  r=json.loads((E/'NFG_K021/receipt.json').read_text());r['copy_patch_sha256']='0'*64
  with self.assertRaises(AssertionError):n.one('NFG_K021',0,r)
 def test_timeout_not_raised(self):
  r=json.loads((E/'NFG_K021/receipt.json').read_text());c=r['native_command'];c[c.index('--harness-timeout')+1]='180s'
  with self.assertRaises(AssertionError):n.one('NFG_K021',0,r)
 def test_source_hash_required(self):
  r=json.loads((E/'NFG_K021/receipt.json').read_text());r['source_hashes']['NFG_src/crates/aspis-core/src/field.rs']='0'*64
  with self.assertRaises(AssertionError):n.one('NFG_K021',0,r)
 def test_fixed_backend_operand(self):
  s=(E/'NFG_chain.rs.txt').read_text().replace('l.m(1,norm,M31(0))','l.m(1,x.a,M31(0))')
  with self.assertRaises(AssertionError):chain(s)
 def test_square_source_operand(self):
  s=(E/'NFG_chain.rs.txt').read_text().replace('l.c(2,x.c1,CM31::ZERO)','l.c(2,x.c0,CM31::ZERO)')
  with self.assertRaises(AssertionError):chain(s)
 def test_source_static(self):
  with self.assertRaises(AssertionError):chain((E/'NFG_chain.rs.txt').read_text()+'\nstatic mut WRONG:u32=0;')
 def test_nonstandard_old_axiom_excluded(self):
  r=json.loads((E/'NFG_L028/receipt.json').read_text());self.assertTrue(any('_native.decide.ax_1' in x for x in r['print_axioms']))
  self.assertEqual(accepted('NFG_QmInvCuts')['attempt'],'NFG_L036')
 def test_exact_six_rows(self):self.assertEqual({r['row'] for r in self.rows},{'TX1:009','TX1:028','TX1:108','TX1:111','TX2:074','TX2:077'})
 def test_trust_retained(self):self.assertEqual(self.delta['trust'],v.obj(v.O/'NFB_LEDGER_DELTA.json')['trust']);self.assertFalse(self.delta['security_target_established'])
if __name__=='__main__':unittest.main(verbosity=2)
