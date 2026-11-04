import unittest,copy
import NEW_validate as v
class Gates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.valid=v.validate(replay=False)
 def setUp(self):self.edges=v.obj(v.E/'NEW_EDGES.json')
 def reject(self,f):
  f(self.edges)
  with self.assertRaises(ValueError):v.validate(self.edges,[],replay=False)
 def test_positive(self):self.assertEqual(self.valid['q_functions_closed'],61)
 def test_roots_open(self):self.assertEqual(set(self.valid['roots'].values()),{'OPEN'})
 def test_promotion(self):self.reject(lambda x:next(e for e in x['edges'] if e['status']=='OPEN').update(status='CLOSED'))
 def test_missing_edge(self):self.reject(lambda x:x['edges'].pop())
 def test_duplicate_edge(self):self.reject(lambda x:x['edges'].__setitem__(1,copy.deepcopy(x['edges'][0])))
 def test_missing_closed_certificate(self):self.reject(lambda x:next(e for e in x['edges'] if e['status']=='CLOSED').update(certificate=None))
 def test_changed_carrier(self):self.reject(lambda x:x['edges'][0].update(callee='unknown'))
 def test_unreviewed_partial(self):
  with self.assertRaises(ValueError):v.validate(self.edges,[dict(root='QueryGeometry::for_range',status='CLOSED')],replay=False)
if __name__=='__main__':unittest.main()
