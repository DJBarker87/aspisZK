"""Source029 only: real Acquisition/Reader APIs, mocked OS, no host reads."""
import hashlib,importlib.util,json,time,unittest
from pathlib import Path
from unittest.mock import patch
import FinalNativeGate_bounded as b
import FinalNativeGate_candidate as c
spec=importlib.util.spec_from_file_location('fixture029',Path(__file__).with_name('FinalNativeGate-v4-tests.py'))
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
class Markers(unittest.TestCase):
 def fixture(self,path,mode=0o100664,uid=1000,gid=1000,raw=b'marker!',nlink=1,data=True):
  t=f.Tree({'STAGE':path});t.nodes[path]=dict(mode=mode,uid=uid,raw=bytearray(raw));original=t.stat
  def metadata(name,dir_fd=None,follow_symlinks=False):
   s=original(name,dir_fd,follow_symlinks)
   if t.path(name,dir_fd)==path:s.st_gid=gid;s.st_nlink=nlink
   return s
  t.stat=metadata;t.api.stat=metadata
  self.enterContext(patch.object(b,'os',t.api));self.enterContext(patch.object(c,'os',t.api))
  a=c.Acquisition(time.monotonic()+10,data_only=data);a.add(path)
  return a,t
 def test_five_exact_paths_and_strict_readers(self):
  plan=json.loads(Path(__file__).with_name('FinalNativeGate-plan.json').read_text())
  paths={p for p in plan['files'] if p.endswith('/.cargo-ok')}
  self.assertEqual(len(paths),5);self.assertEqual(paths,b.DATA_MARKER_PATHS)
  self.assertEqual({plan['files'][p] for p in paths},{'afbf9d0f3560b0fd7795e81c42a0a79ee6b6fc67e064f77826aee642cad28d91'})
  for path in sorted(paths):
   with self.subTest(path=path):
    a,t=self.fixture(path);snap=a.snapshot();self.assertIn(path,snap['pins'])
    row=snap['trusted_group_markers'][0]
    self.assertEqual((row['path'],row['mode'],row['uid'],row['gid'],row['size'],row['nlink']),(path,0o100664,1000,1000,7,1))
    self.assertIn('no-concurrent-untrusted-writer',row['operational_trust'])
    self.assertEqual(b.Reader(a.catalog(),data_only=True).pin(path),snap['pins'][path])
    for kwargs in ({},{'data_only':False}):
     catalog=a.catalog();catalog['data_only']=True
     with self.assertRaisesRegex(b.CatalogError,'writable'):b.Reader(catalog,**kwargs).pin(path)
    c.verify_expected(snap,{path:hashlib.sha256(b'marker!').hexdigest()})
    with self.assertRaisesRegex(b.CatalogError,'fixed source hash drift'):c.verify_expected(snap,{path:plan['files'][path]})
    self.assertFalse(t.fds)
 def test_reject_similar_sixth_and_wrong_metadata_and_strict_acquisition(self):
  path=sorted(b.DATA_MARKER_PATHS)[0]
  for chosen,kwargs in [(path,{'data':False}),(path.replace('/.cargo-ok','-sixth/.cargo-ok'),{}),*( (path,kw) for kw in ({'mode':0o100666},{'mode':0o100774},{'uid':999},{'gid':999},{'raw':b'123456'},{'nlink':2}))]:
   with self.subTest(path=chosen,kwargs=kwargs):
    a,t=self.fixture(chosen,**kwargs);self.assertNotIn(chosen,a.snapshot()['pins']);self.assertFalse(t.fds)
 def test_lifetime_drift_fatal(self):
  path=sorted(b.DATA_MARKER_PATHS)[0];a,t=self.fixture(path);a.snapshot();t.nodes[path]['raw'][:]=b'changed'
  with self.assertRaisesRegex(b.CatalogError,'fixed source hash drift'):
   c.verify_expected(a.snapshot(),{path:hashlib.sha256(b'marker!').hexdigest()})
if __name__=='__main__':unittest.main()
