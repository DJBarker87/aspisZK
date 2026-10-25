import copy,json,pathlib,tempfile,unittest
from Port30JOIN_preflight import exact_name,encode_name,str_name,policy,Reject,bounded_json
N=str_name('A','1')
BASE=dict(schema='Port30JOIN-exact-selection-v1',kernel_enabled=False,base_import='Lean',actual_name_reader=True,
          closure_complete=True,groups_complete=True,sysroot_pins='fixture',raw_byte_pins='fixture',strict_v3_receipt='fixture',
          seeds=[N],choices=[dict(name=N,mode='literal',chosen_origin='original',complete_strict_v3_all_variants=True,
          variants=[dict(origin='original',kind='theorem',unsafe=False,partial=False)])])
class PolicyTests(unittest.TestCase):
 def reject(self,edit):
  d=copy.deepcopy(BASE);edit(d)
  with self.assertRaises(Reject):policy(d)
 def test_num_is_distinct(self):
  self.assertNotEqual(exact_name(N),exact_name(['num',str_name('A'),'1']))
 def test_atomic_dot_is_distinct(self):
  self.assertNotEqual(exact_name(str_name('A.B')),exact_name(str_name('A','B')))
 def test_roundtrip(self):
  for n in [N,['anon'],['num',N,'0'],str_name('_private','M','7','x')]:
   self.assertEqual(encode_name(exact_name(n)),n)
 def test_numeric_canonical(self):
  for n in ['01','-1','','١','1.0']:
   with self.assertRaises(Reject):exact_name(['num',['anon'],n])
 def test_not_kernel_claim(self):self.assertIn('kernel disabled',policy(BASE)['status'])
 def test_enable_rejected(self):self.reject(lambda d:d.update(kernel_enabled=True))
 def test_printed_names_rejected(self):self.reject(lambda d:d.update(actual_name_reader=False))
 def test_missing_closure(self):self.reject(lambda d:d.update(closure_complete=False))
 def test_missing_group(self):self.reject(lambda d:d.update(groups_complete=False))
 def test_weak_guard(self):self.reject(lambda d:d['choices'][0].update(complete_strict_v3_all_variants=False))
 def test_unreviewed_repin(self):self.reject(lambda d:d['choices'][0].update(mode='recheck-current'))
 def test_missing_origin(self):self.reject(lambda d:d['choices'][0].update(chosen_origin='current'))
 def test_axiom(self):self.reject(lambda d:d['choices'][0]['variants'][0].update(kind='axiom'))
 def test_unsafe(self):self.reject(lambda d:d['choices'][0]['variants'][0].update(unsafe=True))
 def test_partial(self):self.reject(lambda d:d['choices'][0]['variants'][0].update(partial=True))
 def test_duplicate_choice(self):self.reject(lambda d:d['choices'].append(copy.deepcopy(d['choices'][0])))
 def test_symlink_no_dereference(self):
  with tempfile.TemporaryDirectory(dir='tools/port30join-20261025') as t:
   p=pathlib.Path(t);(p/'regular').write_text('{}');(p/'link').symlink_to('regular')
   with self.assertRaises(Reject):bounded_json(p/'link')
if __name__=='__main__':unittest.main()
