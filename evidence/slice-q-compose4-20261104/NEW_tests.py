import unittest,copy
import NEW_validate as v
class Gates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.valid=v.validate(replay=False)
 def setUp(self):self.edges=v.obj(v.E/'NEW_EDGES.json');self.certificates=v.obj(v.E/'NEW_CERTIFICATES.json')
 def reject(self,f):
  f(self.edges)
  with self.assertRaises(ValueError):v.validate(self.edges,self.certificates,replay=False)
 def test_positive(self):self.assertEqual(self.valid['q_functions_closed'],62)
 def test_roots_open(self):self.assertEqual(set(self.valid['roots'].values()),{'OPEN'})
 def test_promotion(self):self.reject(lambda x:next(e for e in x['edges'] if e['status']=='OPEN').update(status='CLOSED'))
 def test_missing_edge(self):self.reject(lambda x:x['edges'].pop())
 def test_duplicate_edge(self):self.reject(lambda x:x['edges'].__setitem__(1,copy.deepcopy(x['edges'][0])))
 def test_missing_closed_certificate(self):self.reject(lambda x:next(e for e in x['edges'] if e['status']=='CLOSED').update(certificate=None))
 def test_changed_carrier(self):self.reject(lambda x:x['edges'][0].update(callee='unknown'))
 def test_unreviewed_partial(self):
  with self.assertRaises(ValueError):v.validate(self.edges,[dict(root='QueryGeometry::for_range',status='CLOSED')],replay=False)
 def deny_certificate(self,mutate):
  mutate(self.certificates)
  with self.assertRaises(ValueError):v.validate(self.edges,self.certificates,replay=False)
 def test_missing_result(self):self.deny_certificate(lambda c:c[0]['parts'].remove('full_Result'))
 def test_narrowed_domain(self):self.deny_certificate(lambda c:c[0].update(domain='nonzero only'))
 def test_missing_zero_boundary(self):self.deny_certificate(lambda c:c[0]['parts'].remove('zero_panic_boundary'))
 def test_unproved_callee(self):self.deny_certificate(lambda c:c[0]['remaining_inner_hypotheses'].append('inverse output assumed'))
 def test_old_clone_pair(self):self.deny_certificate(lambda c:c[0]['packet'].update(native_pair=['NEO_K063','NEO_K064']))
 def test_missing_loop(self):self.deny_certificate(lambda c:c[0]['parts'].remove('generic_square_loop'))
 def test_changed_body(self):self.deny_certificate(lambda c:c[0].update(frozen_body_sha256='0'*64))
 def test_new_trust(self):self.deny_certificate(lambda c:c[0]['top_hypotheses'].append('DesiredOutput'))
if __name__=='__main__':unittest.main()
