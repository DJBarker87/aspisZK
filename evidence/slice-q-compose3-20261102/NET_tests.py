import unittest,copy
import NET_validate as v
class Gates(unittest.TestCase):
 def setUp(self):self.edges=v.obj(v.E/'NET_EDGES.json');self.certificates=v.obj(v.E/'NET_CERTIFICATES.json')
 def reject(self,f):
  f(self.edges)
  with self.assertRaises(ValueError):v.validate(self.edges,self.certificates,replay=False)
 def test_positive(self):self.assertEqual(v.validate(replay=False)['q_functions_closed'],56)
 def test_root_status(self):self.assertEqual(set(v.validate(replay=False)['roots'].values()),{'OPEN'})
 def test_missing_edge(self):self.reject(lambda x:x['edges'].pop())
 def test_duplicate_edge(self):self.reject(lambda x:x['edges'].__setitem__(1,copy.deepcopy(x['edges'][0])))
 def test_promotion(self):self.reject(lambda x:next(e for e in x['edges'] if e['status']=='OPEN').update(status='CLOSED'))
 def test_closed_demotion(self):self.reject(lambda x:next(e for e in x['edges'] if e['status']=='CLOSED').update(status='OPEN'))
 def test_missing_certificate(self):self.reject(lambda x:next(e for e in x['edges'] if e['status']=='CLOSED').update(certificate=None))
 def test_replaced_callee(self):self.reject(lambda x:x['edges'][0].update(callee='unknown'))
 def test_replaced_caller(self):self.reject(lambda x:x['edges'][0].update(caller='unknown'))
 def test_source_pin(self):self.reject(lambda x:x['edges'][0].update(source_body_sha256='0'*64))
 def test_window_narrow_domain(self):
  cs=copy.deepcopy(self.certificates);cs[0]['domain']='canonical bytes only'
  with self.assertRaises(ValueError):v.validate(self.edges,cs,replay=False)
 def test_window_no_frame(self):
  cs=copy.deepcopy(self.certificates);cs[0].pop('frame_control')
  with self.assertRaises(ValueError):v.validate(self.edges,cs,replay=False)
 def test_window_old_native_pair(self):
  cs=copy.deepcopy(self.certificates);cs[0]['native_pair']=['NEO_K053','NEO_K054']
  with self.assertRaises(ValueError):v.validate(self.edges,cs,replay=False)
 def test_window_missing_live_allocation(self):
  cs=copy.deepcopy(self.certificates);cs[0]['parts'].remove('same_live_allocation')
  with self.assertRaises(ValueError):v.validate(self.edges,cs,replay=False)
 def test_window_missing_external(self):
  cs=copy.deepcopy(self.certificates);cs[0]['external_obligations'].clear()
  with self.assertRaises(ValueError):v.validate(self.edges,cs,replay=False)
 def test_window_missing_proof(self):
  cs=copy.deepcopy(self.certificates);cs[0]['lean_evidence'].pop()
  with self.assertRaises(ValueError):v.validate(self.edges,cs,replay=False)
 def test_unknown_recipe(self):
  with self.assertRaises(ValueError):v.validate(self.edges,[{'root':'CM31::inv','status':'CLOSED'}],replay=False)
 def test_new_collection(self):self.reject(lambda x:x.update(unreviewed=[]))
if __name__=='__main__':unittest.main()
