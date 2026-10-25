"""Real FixedScope API, mocked OS boundaries. No runtime/kernel validation."""
import errno, unittest
from types import SimpleNamespace as NS
from unittest.mock import patch
import FinalNativeGate_scope as s

class RemovedHandle(unittest.TestCase):
 def exercise(self,*,kind='setup',link=None,info=None,row=None,path=None,fault=None,drift=False,live=False):
  scope=s.FixedScope(kind);scope.fd=8
  cg='/user.slice/'+scope.unit+'.scope'
  old=dict(LoadState='loaded',ActiveState='active',SubState='running',InvocationID='old',ActiveEnterTimestampMonotonic='42',ControlGroup=cg)
  group=[29,4288054,1000,1000,0o40755];scope.binding=dict(unit=old,group=group)
  terminal=dict(old,LoadState='not-found',ActiveState='inactive',SubState='dead',InvocationID='',ControlGroup='') if row is None else dict(old,**row)
  target='/sys/fs/cgroup'+cg+' (deleted)';calls=[0]
  def fstat(fd):
   self.assertEqual(fd,8);calls[0]+=1
   return NS(st_dev=29,st_ino=4288055 if drift and calls[0]>2 else 4288054,st_uid=1000,st_gid=1000,st_mode=0o40755,st_nlink=2)
  def read(name,limit=65536,dir_fd=None):
   if dir_fd==8:
    if live:return 'populated 0\n' if name=='cgroup.events' else ''
    raise FileNotFoundError(errno.ENOENT,'deleted')
   self.assertEqual(name,'/proc/self/fdinfo/8');self.assertEqual(limit,4096)
   if fault=='fdinfo':raise PermissionError(errno.EACCES,'fdinfo')
   return 'pos:\t0\nflags:\t0300000\nmnt_id:\t34\nino:\t4288054\n' if info is None else info
  def readlink(name):
   self.assertEqual(name,'/proc/self/fd/8')
   if fault=='readlink':raise PermissionError(errno.EACCES,'link')
   return target if link is None else link.replace('TARGET',target)
  def stat(pathname,**kw):
   self.assertEqual(pathname,'/sys/fs/cgroup'+cg)
   if fault=='path':raise PermissionError(errno.EACCES,'path')
   if path=='replacement':return NS(st_ino=999)
   raise FileNotFoundError(errno.ENOENT,'absent')
  def show():
   if fault=='show':raise PermissionError(errno.EACCES,'unit')
   return terminal
  with patch.object(s.os,'getuid',return_value=1000),patch.object(s.os,'fstat',side_effect=fstat),patch.object(s.os,'readlink',side_effect=readlink),patch.object(s.os,'stat',side_effect=stat),patch.object(s,'bounded',side_effect=read),patch.object(scope,'show',side_effect=show):
   return scope.empty()
 def reject(self,**kw):
  try:result=self.exercise(**kw)
  except (OSError,ValueError):return
  self.assertFalse(result)
 def test_actual_shape_nlink_two(self):
  for kind in ('setup','final'):
   with self.subTest(kind=kind):self.assertTrue(self.exercise(kind=kind))
 def test_same_inactive(self):
  self.assertTrue(self.exercise(row=dict(ActiveState='inactive',ControlGroup='')))
 def test_live_marker_rejected(self):self.reject(link='/sys/fs/cgroup/user.slice/FinalNativeGate-pin-setup.scope')
 def test_wrong_deleted_marker(self):
  for link in ('TARGET suffix','/other (deleted)','/sys/fs/cgroup/user.slice/FinalNativeGate-pin-setup.scope (deleted) (deleted)'):
   with self.subTest(link=link):self.reject(link=link)
 def test_inode_and_fdinfo(self):
  for info in ('ino: 999\nmnt_id: 34\n','ino: 4288054\n','ino: 4288054\nino: 4288054\nmnt_id: 34\n','malformed'):
   with self.subTest(info=info):self.reject(info=info)
 def test_replacement_unit(self):self.reject(row=dict(InvocationID='new',ActiveState='inactive'))
 def test_replacement_path(self):self.reject(path='replacement')
 def test_rechecked_descriptor(self):self.reject(drift=True)
 def test_errors_never_absence(self):
  for fault in ('fdinfo','readlink','path','show'):
   with self.subTest(fault=fault):self.reject(fault=fault)
 def test_live_empty_unchanged(self):self.assertTrue(self.exercise(live=True))

if __name__=='__main__':unittest.main()
