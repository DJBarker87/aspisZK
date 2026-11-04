import copy,unittest
import NEW_geometry_checks as g
class Receipts(unittest.TestCase):
 def test_correct_pair(self):self.assertFalse(g.pair('NEW_K041','NEW_K042')['composed_credit'])
 def test_old_offline_typo(self):
  with self.assertRaises(AssertionError):g.native('NEW_K011',0)
 def mutate(self,path,change):
  original=g.obj
  def patched(p):
   v=copy.deepcopy(original(p))
   if str(p).endswith(path):change(v)
   return v
  g.obj=patched
  receipt_globals=g.receipt.__globals__
  prior=receipt_globals['obj'];receipt_globals['obj']=patched
  try:
   with self.assertRaises(AssertionError):g.native('NEW_K041',0)
  finally:g.obj=original;receipt_globals['obj']=prior
 def test_offline_removed(self):self.mutate('NEW_K041/receipt.json',lambda r:r['env'].pop('CARGO_NET_OFFLINE'))
 def test_offline_false(self):self.mutate('NEW_K041/receipt.json',lambda r:r['env'].update(CARGO_NET_OFFLINE='false'))
 def test_admission_false(self):self.mutate('NEW_K041-admission.json',lambda r:r['reservation'].update(allowed=False))
 def test_admission_78(self):self.mutate('NEW_K041-admission.json',lambda r:r.update(exit_status=78))
 def test_lock_drift(self):self.mutate('NEW_K041-lock-check.json',lambda r:r.update(after='0'*64))
 def test_graph_drift(self):self.mutate('NEW_K041-graph-check.json',lambda r:r.update(exact_frozen_selected_graph=False))
 def test_bad_patch(self):self.mutate('NEW_K041.json',lambda r:r.update(copy_patch_sha256='0'*64))
 def test_wrong_limit(self):self.mutate('NEW_K041/receipt.json',lambda r:r['limits'].update({'memory.max':'17179869184'}))
 def test_unoptimized(self):self.mutate('NEW_K041/receipt.json',lambda r:r['env'].update(CARGO_PROFILE_DEV_OPT_LEVEL='0'))
if __name__=='__main__':unittest.main()
