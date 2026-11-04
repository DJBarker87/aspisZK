import copy,hashlib,json,tempfile,unittest
from pathlib import Path
import NFB_source_checks as s
import NFB_std_checks as std
import NFB_native_checks as n
from NFB_dependency_check import check_imports
E=Path(__file__).resolve().parent
class Source(unittest.TestCase):
 def test_source(self):self.assertTrue(s.check()['same_final_buffers'])
 def mutation(self,old,new):
  source=(E/'NFB_geometry.rs.txt').read_text();self.assertIn(old,source)
  with self.assertRaises(AssertionError):s.check(source.replace(old,new))
 def test_guard(self):self.mutation('if start>end||end>queries.len()','if start>=end||end>queries.len()')
 def test_record(self):self.mutation('Ok(QueryGeometry{start,inverses,line_z:line_z_values})','Ok(QueryGeometry{start,inverses,line_z:Vec::new()})')
 def test_point_reply(self):self.mutation('domain::Point{x:M31(replies[0]),y:M31(replies[1])}','domain::Point{x:M31(replies[1]),y:M31(replies[0])}')
 def test_right_index(self):self.mutation('FibreIndex::new(u/4*4+3)','FibreIndex::new(u/4*4+2)')
 def test_same_product(self):self.mutation('NFB_row_product(line_x,line_x,M31(replies[4]),log)','NFB_row_product(line_y,line_x,M31(replies[4]),log)')
 def test_log_counter(self):self.mutation('log.len+=1;','log.len+=2;')
 def test_resize_value(self):self.mutation('inverse.resize(next,M31::ZERO);','inverse.resize(next,M31::ONE);')
 def test_static(self):self.mutation('use super::*;','use super::*; static mut NFB_BAD:u32=0;')
 def test_reference_exact_bodies(self):
  ref=(E/'NFB_row_ref.rs.txt').read_text();native=(E/'NFB_geometry.rs.txt').read_text()
  for f in ['NFB_row_call','NFB_row_product','NFB_row']:self.assertEqual(s.tok(s.body(ref,f)),s.tok(s.body(native,f)))
 def test_type_view(self):
  raw=(E/'NFB_row_extracted/NFB_RowRef/Types.lean').read_text()
  view=raw.replace('@[discriminant isize, rust_type "aspis_core::r0::Error"]','@[rust_type "aspis_core::r0::Error"]').replace('@[discriminant isize]\n','')
  self.assertEqual(view,(E/'NFB_RowRef/Types.lean').read_text())
  self.assertNotIn('read_discriminant',(E/'NFB_row_extracted/NFB_RowRef/Funs.lean').read_text())
 def test_std(self):self.assertIn('vec_sha256',std.check())
 def test_std_counter(self):
  text=(E/'NFB_STD_alloc_vec_set_len_on_drop.rs.txt').read_text()
  with self.assertRaises(AssertionError):std.check(guard=text.replace('self.local_len += increment;','self.local_len = increment;'))
 def test_std_clone_iteration(self):
  text=(E/'NFB_STD_alloc_vec_mod.rs.txt').read_text()
  with self.assertRaises(AssertionError):std.check(vec=text.replace('ptr::write(ptr, value.clone());','ptr::write(ptr, value);'))
class Native(unittest.TestCase):
 def test_pair(self):self.assertEqual(n.pair('NFB_K029','NFB_K030')['positive']['exit'],0)
 def test_compile_not_control(self):
  with self.assertRaises(AssertionError):n.native('NFB_K001',1)
 def test_timeout_not_control(self):
  with self.assertRaises(AssertionError):n.native('NFB_K012',1)
 def mutate(self,path,fn):
  def read(p):
   v=copy.deepcopy(n.obj(p))
   if str(p).endswith(path):fn(v)
   return v
  with self.assertRaises(AssertionError):n.native('NFB_K029',0,read)
 def test_offline(self):self.mutate('NFB_K029/receipt.json',lambda r:r['env'].update(CARGO_NET_OFFLINE='false'))
 def test_unoptimized(self):self.mutate('NFB_K029/receipt.json',lambda r:r['env'].update(CARGO_PROFILE_DEV_OPT_LEVEL='0'))
 def test_admission_false(self):self.mutate('NFB_K029-admission.json',lambda r:r['reservation'].update(allowed=False))
 def test_admission_78(self):self.mutate('NFB_K029-admission.json',lambda r:r.update(exit_status=78))
 def test_graph(self):self.mutate('NFB_K029-graph-check.json',lambda r:r.update(exact_frozen_selected_graph=False))
 def test_features(self):
  def change(r):
   next(p for p in r['selected_closure'] if p['name']=='aspis-r1-cost-probe')['features']=[]
  self.mutate('NFB_K029-graph-check.json',change)
 def test_lock(self):self.mutate('NFB_K029-lock-check.json',lambda r:r.update(after='0'*64))
 def test_limits(self):self.mutate('NFB_K029/receipt.json',lambda r:r['limits'].update({'memory.max':'17179869184'}))
 def test_copy_wrong_config(self):
  with self.assertRaises(AssertionError):n.copy_group('NFB_K013','NFB_K014',['NFB_K029'])
class Freshness(unittest.TestCase):
 def fixture(self,root):
  (root/'NFB_A.lean').write_text('import NFB_B\n');(root/'NFB_B.lean').write_text('');(root/'root.lean').write_text('import NFB_A\n')
  records=[]
  for i,m,h in [(1,'NFB_B','b'*64),(2,'NFB_A','a'*64)]:
   a=f'NFB_L{i:03}';d=root/a;d.mkdir();sh=hashlib.sha256((root/(m+'.lean')).read_bytes()).hexdigest()
   records.append(dict(module=m,attempt=a,exit_status=0,source_hashes={m+'.lean':sh},deps_fingerprint=dict(selected_objects={'/private/NFB_B.olean':dict(sha256='b'*64)})))
   (d/'object.json').write_text(json.dumps(dict(module=m,attempt=a,source_sha256=sh,sha256=h)))
  return records
 def case(self,mutate=None,good=False):
  with tempfile.TemporaryDirectory(prefix='NFB_freshness_',dir=E) as td:
   root=Path(td);rs=self.fixture(root)
   if mutate:mutate(root,rs)
   if good:self.assertEqual(set(check_imports(root/'root.lean',root,{},rs)),{'NFB_A','NFB_B'})
   else:
    with self.assertRaises(AssertionError):check_imports(root/'root.lean',root,{},rs)
 def test_good(self):self.case(good=True)
 def test_last_failed(self):self.case(lambda p,r:r.append(dict(r[0],attempt='NFB_L003',exit_status=1)))
 def test_source_drift(self):self.case(lambda p,r:(p/'NFB_B.lean').write_text('-- changed\n'))
 def test_parent_stale(self):self.case(lambda p,r:r[1]['deps_fingerprint']['selected_objects']['/private/NFB_B.olean'].update(sha256='c'*64))
 def test_artifact_wrong_source(self):
  def mutate(p,r):
   f=p/'NFB_L001/object.json';v=json.loads(f.read_text());v['source_sha256']='0'*64;f.write_text(json.dumps(v))
  self.case(mutate)
if __name__=='__main__':unittest.main()
