"""Real collector and adapter; mocked metadata only, no host actions."""
import copy, hashlib, json, unittest
from pathlib import Path
from types import SimpleNamespace as NS
from unittest.mock import Mock, patch
import FinalNativeGate_setup_observe as o
import FinalNativeGate_setup_adapter as a
import FinalNativeGate_scope as scope
RACE='ValueError: hierarchy/structural/control race'
class FreshPairs(unittest.TestCase):
 def exercise(self,errors,*,fault=None,step=0):
  clock=[0.];saved={};scans=[];evaluated=[];timeouts=[];commands=[];guard=Mock()
  if fault=='guard':guard.check.side_effect=ValueError('guard exception')
  def scan():
   value={'fresh':len(scans)+1};scans.append(value);return value
  def evaluate(old,before,after,requested,**kw):
   evaluated.append((old,before,after));clock[0]+=step
   error=errors[min(len(evaluated)-1,len(errors)-1)]
   if fault=='control':raise ValueError('control exception')
   d=dict(allowed=True,cap_ok=True,available_ok=True,legacy_nonreserve_gate_ok=True,
          min_mem_available_bytes=20*a.c.GIB,projected_reserved_bytes=a.c.GIB,requested_bytes=requested)
   if error:d.update(allowed=False,error=error)
   return d
  def command(args,**kwargs):
   timeouts.append(kwargs['timeout']);commands.append(list(args))
   self.assertGreater(kwargs['timeout'],0);self.assertLessEqual(kwargs['timeout'],min(15,30-clock[0]))
   stdout='PID PPID RSS COMMAND CGROUP\n1 0 1 init /\n' if args==a.COMMANDS[0] else ''
   return NS(returncode=0,stdout=stdout,stderr='')
  def save(name,value):
   if fault=='reporter':raise ValueError('reporter exception')
   self.assertNotIn(name,saved);saved[name]=copy.deepcopy(value)
   raw=json.dumps(value).encode();return dict(name=name,size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
  original=(Path.read_text,o.subprocess.run,o.os.scandir);admission=[]
  with patch.object(o,'ACTIVE_GUARD',guard),patch.object(o.time,'monotonic',side_effect=lambda:clock[0]),patch.object(o,'save',side_effect=save),patch.dict(a.inventory,inventory=Mock(return_value=[])),patch.dict(a.identity,scan_bound=scan),patch.object(a.policy,'evaluate',side_effect=evaluate),patch.object(scope,'command',side_effect=command):
   if fault or step>=20:
    with self.assertRaises((ValueError,TimeoutError)):o.collect('inside-scope',admission)
    result=None
   else:result=o.collect('inside-scope',admission)
  self.assertEqual((Path.read_text,o.subprocess.run,o.os.scandir),original)
  return result,admission,saved,scans,evaluated,commands,timeouts
 def test_failed_pair_then_fully_fresh_success(self):
  r,ad,saved,scans,ev,cmd,_=self.exercise([RACE,None])
  self.assertTrue(r['decision']['allowed']);self.assertEqual(len(ev),2)
  self.assertEqual([x['fresh'] for x in scans],[1,2,3,4]);self.assertIsNot(ev[0][0],ev[1][0])
  self.assertEqual(len(cmd),6);self.assertEqual(len(saved),6);self.assertEqual(len(ad),2)
  self.assertEqual(saved['attempt1-inside-scope-report.json']['decision']['error'],RACE)
  self.assertEqual(saved['attempt2-inside-scope-report.json']['snapshots']['before'],{'fresh':3})
  self.assertTrue(saved['attempt1-inside-scope-ordered.json']);self.assertEqual(len(ad[0]['full_evidence']),3)
  self.assertNotEqual(ad[0]['full_evidence'][0]['name'],ad[1]['full_evidence'][0]['name'])
 def test_three_exhausted(self):
  r,ad,saved,scans,ev,cmd,_=self.exercise([RACE]);self.assertFalse(r['decision']['allowed'])
  self.assertEqual((len(ev),len(scans),len(cmd),len(saved),len(ad)),(3,6,9,9,3))
 def test_other_denial_once(self):
  for error in ('own identity','cap exceeded','unknown',RACE+' '):
   with self.subTest(error=error):self.assertEqual(len(self.exercise([error])[4]),1)
 def test_exceptions_never_retry(self):
  for fault in ('guard','control','reporter'):
   with self.subTest(fault=fault):self.assertLessEqual(len(self.exercise([RACE],fault=fault)[4]),1)
 def test_shared_deadline_and_command_remaining(self):
  result=self.exercise([RACE,None],step=20)
  self.assertIsNone(result[0]);self.assertEqual(len(result[4]),2)
  self.assertEqual(result[6][-3:],[10]*3)
 def test_remaining_command_timeout(self):
  r,ad,saved,scans,ev,cmd,timeouts=self.exercise([RACE,None],step=8)
  self.assertEqual(timeouts,[15]*6)
if __name__=='__main__':unittest.main()
