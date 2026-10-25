"""Concrete Proc -> Guard -> cleanup join; Linux OS controls mocked, no PID signals."""
import errno
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import Mock, patch
E=Path(__file__).resolve().parent
D=Path(os.environ.get('FINAL_NATIVE_JOIN_SOURCE',str(E.parents[3]/'tools/prover-rw-20261023/final-native-gate')))
sys.path.insert(0,str(D))
import FinalNativeGate_guard as g
import FinalNativeGate_cleanup as consumer

class Join(unittest.TestCase):
    def proc(self,absence=True,start=101):
        p=g.Proc();p.absent=Mock(return_value=absence)
        fields=['S','12']+['0']*17+[str(start),'0','3']
        def read(path):
            if path=='/proc/14/stat':return '14 (owned child) '+' '.join(fields)
            if path=='/proc/14/status':return 'Tgid: 14\nPid: 14\n'
            raise AssertionError(path)
        p.read=Mock(side_effect=read)
        return p

    def join(self,p,*,scope=None,outer=False,spawn_state=None):
        guard=g.Guard(proc=p,pid=12,notify=Mock())
        guard.owned={12:99,14:101}
        guard.thread=Mock();guard.thread.is_alive.return_value=False
        result=consumer.cleanup(None,None,None,guard,Mock(side_effect=AssertionError('no direct child')),scope,
                                outer=outer,spawn_state=spawn_state)
        self.assertEqual(guard.owned,{12:99,14:101})
        self.assertEqual(result['monitor']['cancellations'],guard.cancelled)
        return result,guard

    def test_verified_already_gone_closed_join(self):
        p=self.proc()
        with patch.object(g.os,'pidfd_open',side_effect=ProcessLookupError(errno.ESRCH,'gone'),create=True), \
             patch.object(g.os,'close') as close, \
             patch.object(g.signal,'pidfd_send_signal',create=True) as signal:
            result,guard=self.join(p)
        self.assertEqual(result['errors'],[])
        self.assertEqual(guard.cancelled,[dict(pid=14,starttime=101,outcome='disappeared')])
        signal.assert_not_called();close.assert_not_called()
        event=result['monitor']['proc_events'][-1]
        self.assertEqual(event['operation'],'pidfd-open')
        self.assertEqual(event['independent_absence'],dict(path='/proc/14',absent=True))
        self.assertEqual(event['known_stable_identity'],dict(pid=14,tgid=14,starttime=101))

    def test_absence_after_open_closed_join_and_fd_closed(self):
        p=self.proc();p.read.side_effect=ProcessLookupError(errno.ESRCH,'gone after open')
        with patch.object(g.os,'pidfd_open',return_value=77,create=True),patch.object(g.os,'close') as close, \
             patch.object(g.signal,'pidfd_send_signal',create=True) as signal:
            result,_=self.join(p)
        self.assertEqual(result['errors'],[]);self.assertEqual(result['monitor']['cancellations'][0]['outcome'],'disappeared')
        close.assert_called_once_with(77);signal.assert_not_called()
        self.assertEqual(p.events[-1]['operation'],'read-stat')

    def test_verified_signal_esrch_closed_join_and_finally_close(self):
        p=self.proc()
        with patch.object(g.os,'pidfd_open',return_value=77,create=True),patch.object(g.os,'close') as close, \
             patch.object(g.signal,'pidfd_send_signal',side_effect=ProcessLookupError(errno.ESRCH,'gone at signal'),create=True) as signal:
            result,_=self.join(p)
        self.assertEqual(result['errors'],[])
        self.assertEqual(result['monitor']['cancellations'][0]['outcome'],'disappeared')
        signal.assert_called_once_with(77,g.signal.SIGKILL);close.assert_called_once_with(77)
        self.assertEqual(p.events[-1]['operation'],'pidfd-signal')
        self.assertTrue(p.events[-1]['independent_absence']['absent'])

    def test_invalid_live_unknown_permission_open_fail_closed(self):
        for absence,error in ((False,ProcessLookupError(3,'live')),(None,ProcessLookupError(3,'unknown')),
                              (True,PermissionError(13,'denied')),(True,ProcessLookupError(5,'wrong errno'))):
            with self.subTest(absence=absence,error=repr(error)):
                p=self.proc(absence)
                with patch.object(g.os,'pidfd_open',side_effect=error,create=True),patch.object(g.os,'close') as close, \
                     patch.object(g.signal,'pidfd_send_signal',create=True) as signal:
                    result,_=self.join(p)
                self.assertTrue(any('descendant unresolved' in x for x in result['errors']))
                self.assertTrue(result['monitor']['cancellations'][0]['outcome'].startswith('cancellation-error:'))
                close.assert_not_called();signal.assert_not_called()
        p=self.proc();p.absent.side_effect=PermissionError(13,'unknown visibility')
        with patch.object(g.os,'pidfd_open',side_effect=ProcessLookupError(3,'gone?'),create=True):
            result,_=self.join(p)
        self.assertTrue(result['errors']);self.assertIn('error',p.events[-1]['independent_absence'])

    def test_signal_live_unknown_permission_fail_closed_and_fd_closed(self):
        for absence,error in ((False,ProcessLookupError(3,'live')),(None,ProcessLookupError(3,'unknown')),
                              (True,PermissionError(13,'denied'))):
            with self.subTest(absence=absence,error=repr(error)):
                p=self.proc(absence)
                with patch.object(g.os,'pidfd_open',return_value=77,create=True),patch.object(g.os,'close') as close, \
                     patch.object(g.signal,'pidfd_send_signal',side_effect=error,create=True):
                    result,_=self.join(p)
                self.assertTrue(result['errors']);close.assert_called_once_with(77)
                self.assertEqual(p.events[-1]['operation'],'pidfd-signal')

    def test_reused_pid_not_signalled_remains_unresolved(self):
        p=self.proc(start=102)
        with patch.object(g.os,'pidfd_open',return_value=77,create=True),patch.object(g.os,'close') as close, \
             patch.object(g.signal,'pidfd_send_signal',create=True) as signal:
            result,_=self.join(p)
        self.assertEqual(result['monitor']['cancellations'][0]['outcome'],'reused-not-signalled')
        self.assertTrue(result['errors']);signal.assert_not_called();close.assert_called_once_with(77)

    def test_live_owned_signal_compatible(self):
        p=self.proc()
        with patch.object(g.os,'pidfd_open',return_value=77,create=True),patch.object(g.os,'close') as close, \
             patch.object(g.signal,'pidfd_send_signal',create=True) as signal:
            result,_=self.join(p)
        self.assertEqual(result['errors'],[])
        self.assertEqual(result['monitor']['cancellations'][0]['outcome'],'verified-owned-signalled')
        close.assert_called_once_with(77);signal.assert_called_once_with(77,g.signal.SIGKILL)

    def test_verified_disappearance_does_not_waive_uncertain_outer_control(self):
        p=self.proc();scope=Mock(fd=None,binding=None);scope.finish.return_value=dict(unresolved=True)
        with patch.object(g.os,'pidfd_open',side_effect=ProcessLookupError(3,'gone'),create=True):
            result,_=self.join(p,scope=scope,outer=True,spawn_state='uncertain')
        self.assertTrue(result['unresolved']);self.assertTrue(any('SCOPE_UNRESOLVED' in x for x in result['errors']))
        scope.cancel_owned.assert_called_once();scope.finish.assert_called_once();scope.close.assert_not_called()

if __name__=='__main__':unittest.main(verbosity=2)
