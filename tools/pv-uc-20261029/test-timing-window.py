"""Offline guard tests. Synthetic markers/cgroups only; no SSH or timing call."""
from pathlib import Path
import importlib.util,json,tempfile,unittest
s=importlib.util.spec_from_file_location('guard',Path(__file__).with_name('timing-window-guard.py'));g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
class Tests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name);self.m=self.root/'QUIET_WINDOW.json'
 def tearDown(self):self.tmp.cleanup()
 def marker(self,x):self.m.write_text(json.dumps(x))
 def test_live_own(self):
  self.marker({'until':101,'for':'pv-uc-timing'});before=self.m.read_bytes()
  self.assertTrue(g.marker_guard(self.m,100,True)['owner_exception']);self.assertEqual(before,self.m.read_bytes())
 def test_live_foreign(self):
  for name in ['Stream A','pv-c474-20261029','',None]:
   self.marker({'until':101,'for':name})
   with self.assertRaises(g.Hold):g.marker_guard(self.m,100)
 def test_live_missing_for(self):
  self.marker({'until':101,'owner':'pv-uc-timing'})
  with self.assertRaises(g.Hold):g.marker_guard(self.m,100)
 def test_expired(self):
  for until in [99,100]:
   self.marker({'until':until,'for':'foreign'});self.assertFalse(g.marker_guard(self.m,100)['active'])
   with self.assertRaises(g.Hold):g.marker_guard(self.m,100,True)
 def test_absent(self):
  self.assertTrue(g.marker_guard(self.m,100)['allowed'])
  with self.assertRaises(g.Hold):g.marker_guard(self.m,100,True)
 def test_malformed(self):
  for raw in ['{','null','[]','{}','{"until":"101"}','{"until":true}','{"until":NaN}','{"until":Infinity}']:
   self.m.write_text(raw)
   with self.assertRaises(g.Hold):g.marker_guard(self.m,100)
 def test_unreadable(self):
  self.m.mkdir()
  with self.assertRaises(g.Hold):g.marker_guard(self.m,100)
 def group(self,p,cap='max',pop='1'):
  p.mkdir(parents=True);(p/'memory.max').write_text(cap);(p/'cgroup.events').write_text('populated '+pop+'\nfrozen 0\n')
 def test_scope_inventory(self):
  root=self.root/'user.slice';self.group(root)
  own=root/'user-1.slice/own.scope';self.group(own.parent);self.group(own,'8589934592');self.group(own/'child','100')
  foreign=root/'user-2.slice/foreign.scope';self.group(foreign.parent);self.group(foreign,'8589934592')
  empty=root/'empty.scope';self.group(empty,'8589934592','0')
  self.assertEqual([r['cgroup'] for r in g.foreign_scopes(root,own)],[str(foreign)])
 def test_inventory_race_refuses(self):
  root=self.root/'user.slice';self.group(root);(root/'missing').mkdir()
  with self.assertRaises(g.Hold):g.foreign_scopes(root,self.root/'own')
 def test_pair_invalidation_sticky(self):
  probes=iter([{'quiet':True},g.Hold('other capped scope: synthetic'),{'quiet':True}])
  def probe():
   r=next(probes)
   if isinstance(r,Exception):raise r
   return r
  m=g.Monitor(probe=probe);m.poll()
  with self.assertRaises(g.Hold):m.poll()
  self.assertIn('other capped scope',m.failure['reason'])
  with self.assertRaises(g.Hold):m.poll()
 def test_background_monitor_stops(self):
  import threading
  entered=threading.Event()
  def probe():
   if entered.is_set():raise g.Hold('other capped scope: synthetic during call')
   return {}
  m=g.Monitor(probe,interval=0.001)
  with m:
   entered.set()
   # Event wait is a test timeout, never a host/timing process.
   for _ in range(100):
    if m.failure:break
    threading.Event().wait(0.001)
   self.assertIsNotNone(m.failure)
   with self.assertRaises(g.Hold):m.poll()
  self.assertFalse(m.thread.is_alive())
if __name__=='__main__':unittest.main(verbosity=2)
