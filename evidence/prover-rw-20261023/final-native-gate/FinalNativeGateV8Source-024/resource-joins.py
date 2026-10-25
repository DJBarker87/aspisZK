"""Tiny synthetic joins through actual privacy adapters; no live collectors invoked."""
import ast,copy,hashlib,json,pathlib,resource,sys,time,unittest
from unittest.mock import patch
START=time.monotonic();D=pathlib.Path('tools/prover-rw-20261023/final-native-gate');sys.path.insert(0,str(D.resolve()))
import FinalNativeGate_policy as loader
import FinalNativeGate_setup_adapter as setup
import FinalNativeGate_adapter as final
c=setup.c;G=c.GIB
fx=loader.functions(loader.load_bundle()['fixtures']['source'],['node','fixture','legacy','scope'],dict(c=c,G=G))
class Joins(unittest.TestCase):
 def result(self,s,after=None):
  old=dict(cgroups=[dict(path=r['path'],charged_bytes=r['cap']) for r in s['rows'] if not r['root']],projected_reserved_bytes=sum(r['cap'] for r in s['rows'] if not r['root'])+G,allowed=True,reserve_check=True,process_visibility='mock processes',service_visibility='',docker_visibility=[])
  with patch.object(setup,'visibility',return_value=old),patch.dict(setup.identity,scan_bound=unittest.mock.Mock(side_effect=[s,s if after is None else after])):
   return setup.read_only_admission(phase='prospective')['decision']
 def test_positive_and_pid_residual(self):
  s,e=fx['scope'](768*2**20,G);s['rows'][0]['subtree_pids']=True;s['rows'][1].update(pids_enabled=True,pids_current=2,tasks_max=64)
  d=self.result(s);self.assertTrue(d['allowed'],d);self.assertEqual(d['requested_bytes'],G)
  s['rows'][1]['pids_current']=1;equal=self.result(s);self.assertTrue(equal['allowed']);self.assertEqual(d['projected_reserved_bytes'],equal['projected_reserved_bytes'])
 def test_invalid_and_missing_pid(self):
  for value in (-1,True,None,65):
   s,e=fx['scope'](768*2**20,G);s['rows'][0]['subtree_pids']=True;s['rows'][1].update(pids_enabled=True,pids_current=value,tasks_max=64)
   self.assertFalse(self.result(s)['allowed'])
 def test_structural_and_collection_error(self):
  s,e=fx['scope'](768*2**20,G);s['rows'][1]['parent']='/wrong';self.assertFalse(self.result(s)['allowed'])
  with patch.object(setup,'visibility',side_effect=ValueError('mock denied')),patch.dict(setup.identity,scan_bound=lambda:None):
   self.assertFalse(setup.read_only_admission(phase='prospective')['decision']['allowed'])
 def decision(self):return dict(allowed=False,cap_ok=True,available_ok=True,legacy_nonreserve_gate_ok=True,min_mem_available_bytes=20*G,projected_reserved_bytes=9*G,requested_bytes=G)
 def test_diagnostic_only_and_exact_import(self):
  for a in (setup,final):
   d=a.operational_admission(self.decision(),{});self.assertTrue(d['allowed']);self.assertFalse(d['conservative_adjusted_policy_allowed'])
  self.assertEqual(setup.EXPECTED,dict(high=768*2**20,cap=G,swap_max=0,tasks_max=64));self.assertEqual(final.EXPECTED,dict(high=3*G,cap=4*G,swap_max=0,tasks_max=64))
 def test_fail_closed_missing_invalid_error_structural(self):
  for a in (setup,final):
   for key in ('min_mem_available_bytes','projected_reserved_bytes','requested_bytes'):
    for val in (None,-1,True,'1'):
     d=self.decision();d[key]=val;self.assertFalse(a.operational_admission(d,{})['allowed'])
    d=self.decision();del d[key];self.assertFalse(a.operational_admission(d,{})['allowed'])
   for key in ('cap_ok','available_ok','legacy_nonreserve_gate_ok'):
    d=self.decision();d[key]=False;self.assertFalse(a.operational_admission(d,{})['allowed'])
   d=self.decision();d['error']='invalid hierarchy';self.assertFalse(a.operational_admission(d,{})['allowed']);self.assertFalse(a.operational_admission(self.decision(),{'before':'denied'})['allowed'])
 def test_strict_equalities(self):
  for a in (setup,final):
   for changes in (dict(min_mem_available_bytes=16*G),dict(projected_reserved_bytes=55*G,min_mem_available_bytes=100*G),dict(projected_reserved_bytes=0,min_mem_available_bytes=3*G)):
    d=self.decision();d.update(changes);self.assertFalse(a.operational_admission(d,{})['allowed'])
 def test_real_evaluator_adjusted_only_failure(self):
  s,e=fx['scope'](768*2**20,G);s['meminfo']['Active(file)']=75*G
  d=self.result(s);self.assertTrue(d['allowed'],d);self.assertFalse(d['conservative_adjusted_policy_allowed'])
 def test_inside_scope_own_cap_once_and_identity(self):
  s,e=fx['scope'](768*2**20,G)
  for r in s['rows']:
   for k in ('path','domain'):
    r[k]=r[k].replace('job.scope',setup.UNIT+'.scope')
  for k in ('path','unified_path'):s['self_observation'][k]=s['self_observation'][k].replace('job.scope',setup.UNIT+'.scope')
  old=fx['legacy'](s,0)
  with patch.object(setup,'visibility',return_value=old),patch.dict(setup.identity,scan_bound=lambda:s):
   d=setup.read_only_admission(phase='inside-scope')['decision'];self.assertTrue(d['allowed'],d);self.assertEqual(d['projected_reserved_bytes'],G);self.assertEqual(d['requested_bytes'],0)
  after=copy.deepcopy(s);after['self_observation']['starttime']+=1
  with patch.object(setup,'visibility',return_value=old),patch.dict(setup.identity,scan_bound=unittest.mock.Mock(side_effect=[s,after])):
   self.assertFalse(setup.read_only_admission(phase='inside-scope')['decision']['allowed'])
 def test_structural_between_scans(self):
  s,e=fx['scope'](768*2**20,G);after=copy.deepcopy(s);after['rows'][-1]['tasks_max']=63
  self.assertFalse(self.result(s,after)['allowed'])
 def test_visible_exceeds_charged(self):
  s,e=fx['scope'](768*2**20,G);s['rows'][-1]['pids_current']=0
  self.assertTrue(self.result(s)['allowed'])
  baseline=c.observe(s)
  for count in (0,1,2):
   s['rows'][-1]['pids_current']=count
   self.assertEqual(c.observe(s),baseline)
   self.assertTrue(self.result(s)['allowed'])

class Focused(Joins):
 def result(self,s,after=None):
  decisions=[]
  for adapter,request in ((setup,G),(final,4*G)):
   old=dict(cgroups=[dict(path=r['path'],charged_bytes=r['cap']) for r in s['rows'] if not r['root']],projected_reserved_bytes=sum(r['cap'] for r in s['rows'] if not r['root'])+request,allowed=True,reserve_check=True,process_visibility='mock processes',service_visibility='',docker_visibility=[])
   with patch.object(adapter,'visibility',return_value=old),patch.dict(adapter.identity,scan_bound=unittest.mock.Mock(side_effect=[s,s if after is None else after])):
    decisions.append(adapter.read_only_admission(phase='prospective')['decision'])
  assert decisions[0]['allowed']==decisions[1]['allowed'],decisions
  return decisions[0]
 def test_missing_identity_controls_and_errors(self):
  for change in ('missing','duplicate','tgid','domain','control'):
   s,e=fx['scope'](768*2**20,G)
   row=s['rows'][-1]
   if change=='missing':del row['pids_current']
   elif change=='duplicate':row['threads']*=2
   elif change=='tgid':row['identities'][0]['tgid']=999
   elif change=='domain':row['domain']='/wrong'
   else:row['tasks_max']=-1
   self.assertFalse(self.result(s)['allowed'],change)
  for a in (setup,final):
   with patch.object(a,'visibility',side_effect=ValueError('synthetic denied')),patch.dict(a.identity,scan_bound=unittest.mock.Mock(side_effect=PermissionError('synthetic scan'))):
    self.assertFalse(a.read_only_admission(phase='prospective')['decision']['allowed'])

if __name__=='__main__':
 result=unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(Focused(n) for n in ('test_positive_and_pid_residual','test_invalid_and_missing_pid','test_structural_and_collection_error','test_visible_exceeds_charged','test_missing_identity_controls_and_errors')))
 r=resource.getrusage(resource.RUSAGE_SELF)
 receipt=dict(argv=[sys.executable,'-B',__file__],exit=0 if result.wasSuccessful() else 1,wall_seconds=time.monotonic()-START,peak_rss_bytes=r.ru_maxrss,swap=r.ru_nswap,source_revision='c03e7860d3bc6b8e2bf1af961bffa779bfc7126a plus source-024',print_axioms='N/A',host_actions=0)
 pathlib.Path(__file__).with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');sys.exit(receipt['exit'])
