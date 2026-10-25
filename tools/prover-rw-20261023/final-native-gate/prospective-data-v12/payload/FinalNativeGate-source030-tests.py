"""Real FixedScope/cleanup APIs; all OS/clock boundaries mocked, no host calls."""
import json
import unittest
from types import SimpleNamespace as NS
from unittest.mock import Mock,patch
import FinalNativeGate_scope as s
import FinalNativeGate_cleanup as c
ROW=dict(LoadState='loaded',ActiveState='active',SubState='running',InvocationID='a'*32,
         ActiveEnterTimestampMonotonic='100',ControlGroup='/user.slice/FinalNativeGate-pin-setup.scope')
READY=dict(pid=12,ppid=11,starttime=120,cgroup=ROW['ControlGroup'])
WRAPPER=dict(pid=11,starttime=110,ppid=1)
START=dict(ROW,ActiveState='activating',InvocationID='',ActiveEnterTimestampMonotonic='0')
class Source030(unittest.TestCase):
    def exercise(self,mode):
        scope=s.FixedScope('setup');clock=[0.0];calls=[0]
        child=NS(poll=Mock(return_value=None),returncode=0)
        guard=Mock();guard.finish.return_value={}
        if mode=='guard':guard.check.side_effect=ValueError('guard failed')
        def command(*args,**kwargs):
            calls[0]+=1
            row=START if calls[0]==1 or mode=='timeout' else dict(ROW)
            if calls[0]>2 and mode=='replacement':row['InvocationID']='b'*32
            if mode=='exit' and calls[0]==1:child.poll.return_value=0
            return ''.join(k+'='+v+'\n' for k,v in row.items())
        def opening(cg):scope.fd=99
        scope.open_group=Mock(side_effect=opening);scope.group_identity=Mock(return_value=[1,2,3])
        def read(name):
            values={'memory.high':str(scope.high),'memory.max':str(scope.cap),'memory.swap.max':'0','pids.max':'64','memory.swap.current':'0','cgroup.procs':'12'}
            return '1' if mode=='control' and name=='memory.swap.max' else values[name]
        scope.read=Mock(side_effect=read)
        proc=Mock();proc.identity.side_effect=lambda pid:dict(READY,starttime=121 if mode=='pid' else 120) if pid==12 else WRAPPER
        with patch.object(s,'command',side_effect=command),patch.object(s,'bounded',return_value=json.dumps(READY)),patch.object(s,'Proc',return_value=proc),patch.object(s,'membership',side_effect=lambda pid:'/' if pid==1 else ROW['ControlGroup']),patch.object(s.os,'getpid',return_value=1),patch.object(s.time,'monotonic',side_effect=lambda:clock[0]),patch.object(s.time,'sleep',side_effect=lambda seconds:clock.__setitem__(0,clock[0]+seconds)),patch.object(s,'durable') as write:
            if mode=='valid':
                scope.bind_release(child,WRAPPER,guard)
                self.assertEqual([x.args[1] for x in write.call_args_list],['scope-binding.json','scope-release.json'])
                self.assertGreater(scope.read.call_count,8);self.assertGreater(proc.identity.call_count,2)
            else:
                with self.assertRaises(TimeoutError if mode=='timeout' else ValueError):scope.bind_release(child,WRAPPER,guard)
                write.assert_not_called()
            guard.check.assert_called()
        return scope,guard,child
    def test_starting_then_valid_all_ownership_checks(self):self.exercise('valid')
    def test_wrapper_replacement_pid_control_reject(self):
        for mode in ('exit','replacement','pid','control','guard'):
            with self.subTest(mode=mode):self.exercise(mode)
    def test_never_valid_original_deadline_retains_cleanup_evidence(self):
        scope,guard,child=self.exercise('timeout')
        self.assertIsNone(scope.binding);self.assertEqual(len(scope.events),8)
        self.assertEqual(scope.prebind_failure['failed_fields'],['ActiveState','InvocationID','ActiveEnterTimestampMonotonic'])
        result=c.cleanup(child,None,None,guard,Mock(),scope,outer=True,spawn_state='started')
        self.assertTrue(result['unresolved']);self.assertIsNone(result['scope']['binding'])
        self.assertEqual(result['scope']['events'],scope.events)
        self.assertEqual(result['scope']['prebind_failure'],scope.prebind_failure)
        self.assertIn('ActiveState=activating',result['scope']['events'][-1]['raw'])
        self.assertLess(len(json.dumps(result).encode()),5_000_000)
    def test_malformed_raw_retained(self):
        scope=s.FixedScope('setup')
        with patch.object(s,'command',return_value='broken-row'),self.assertRaises(ValueError):scope.show()
        self.assertEqual(scope.events[-1]['raw'],'broken-row')
if __name__=='__main__':unittest.main()
