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
 def test_marker_changes_during_pair(self):
  import time
  self.marker({'until':time.time()+100,'for':'pv-uc-timing'})
  m=g.Monitor(lambda:g.check(self.m,True,lambda:[]));m.poll()
  self.marker({'until':time.time()+100,'for':'foreign'})
  with self.assertRaises(g.Hold):m.poll()
  self.marker({'until':time.time()+100,'for':'pv-uc-timing'})
  with self.assertRaises(g.Hold):m.poll()
 def test_foreign_scope_terminates_client_process(self):
  # Load only invoke's AST. Never import/execute timing-window.py's main body.
  import ast,os,signal,subprocess,sys
  tree=ast.parse(Path(__file__).with_name('timing-window.py').read_text())
  fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='invoke')
  spawned=[];real_popen=subprocess.Popen
  class Popen(real_popen):
   def __init__(self,*args,**kwargs):super().__init__(*args,**kwargs);spawned.append(self)
  from types import SimpleNamespace
  api=SimpleNamespace(Popen=Popen,PIPE=subprocess.PIPE,TimeoutExpired=subprocess.TimeoutExpired,CompletedProcess=subprocess.CompletedProcess)
  m=g.Monitor(lambda:(_ for _ in ()).throw(g.Hold('other capped scope: synthetic')))
  scope=dict(subprocess=api,os=os,signal=signal,monitor=m,result_input='')
  exec(compile(ast.Module(body=[fn],type_ignores=[]),'<offline invoke only>','exec'),scope)
  with self.assertRaises(g.Hold):
   scope['invoke']([sys.executable,'-c','import time; time.sleep(5)'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
  self.assertEqual(len(spawned),1);self.assertIsNotNone(spawned[0].poll())
  self.assertIsNotNone(m.failure)
 def test_short_lived_scope_event_survives_empty_inventory(self):
  events=g.ScopeEvents(own_unit='pv-uc-native91120.scope')
  events.feed_unit('pv-uc-native91120.scope');events.feed_unit('background.service')
  self.assertFalse(events.history)
  events.feed_unit('foreign-transient.scope')
  m=g.Monitor(probe=lambda:{'foreign_capped_scopes':[]});m.events=events
  with self.assertRaises(g.Hold):m.poll()
  self.assertEqual(m.failure['event']['unit'],'foreign-transient.scope')
 def test_event_stream_failure_refuses(self):
  events=g.ScopeEvents(own_unit='own.scope');events.failure={'reason':'event stream disconnected'}
  m=g.Monitor(probe=lambda:{});m.events=events
  with self.assertRaises(g.Hold):m.poll()
 def test_event_subscription_failure_cleans_up(self):
  class Fake:
   failure=None
   def start(self):raise g.Hold('subscription unavailable')
   def close(self):self.closed=True
  fake=Fake();original=g.ScopeEvents;g.ScopeEvents=lambda:fake
  try:
   with self.assertRaises(g.Hold):g.Monitor(probe=lambda:{},event_watch=True).start()
   self.assertTrue(fake.closed)
  finally:g.ScopeEvents=original
 def test_scope_id_and_caps(self):
  limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  self.assertEqual(g.scope_identifier('pv-uc-native91120.scope',limits),'native91120')
  for name in ['pv-uc-native90115.scope','pv-uc-native91119.scope','pv-uc-native75115.scope','pv-uc-native91126.scope','session-1.scope']:
   with self.assertRaises(g.Hold):g.scope_identifier(name,limits)
  for key in limits:
   bad=dict(limits);bad[key]='max'
   with self.assertRaises(g.Hold):g.scope_identifier('pv-uc-native91120.scope',bad)
 def test_final_client_pipe_wiring(self):
  # Execute only the request/FD setup and cleanup with a synthetic caller.
  # No client, runner main body, scope, fixture secret, or timing is executed.
  import ast,os,subprocess,time
  from types import SimpleNamespace
  tree=ast.parse(Path(__file__).with_name('timing-window.py').read_text())
  loop=next(n for n in ast.walk(tree) if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='side')
  start=next(i for i,n in enumerate(loop.body) if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='rfd')
  end=next(i for i,n in enumerate(loop.body) if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='wall')
  block=ast.Module(body=loop.body[start:end],type_ignores=[])
  record=bytes(range(212));seen=[]
  def invoke(command,**kwargs):
   fds=kwargs['pass_fds'];self.assertEqual(len(fds),2)
   self.assertNotEqual(os.fstat(fds[0]).st_ino,os.fstat(fds[1]).st_ino)
   self.assertEqual(os.read(fds[0],213),record)
   os.write(fds[1],record);seen.extend(fds)
   return SimpleNamespace(returncode=0,stdout='{}',stderr='')
  scope=dict(os=os,json=json,subprocess=subprocess,time=time,side='draft',q={'note':{}},fixtures={'lane_leaf_sets':[], 'records':[record.hex(),record.hex()]},f='transfer',B={'draft':'synthetic-unused'},invoke=invoke)
  exec(compile(block,'<offline pipe wiring only>','exec'),scope)
  self.assertEqual(scope['custody'],record)
  for fd in [*seen,scope['output_read']]:
   with self.assertRaises(OSError):os.fstat(fd)
if __name__=='__main__':unittest.main(verbosity=2)
