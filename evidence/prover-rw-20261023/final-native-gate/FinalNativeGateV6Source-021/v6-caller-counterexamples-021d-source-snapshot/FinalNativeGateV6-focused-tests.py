"""Mock-only v6 source gates; no SSH, signals, native code, or process launch."""
import errno
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch
E=Path(__file__).resolve().parent
D=E.parents[3]/'tools/prover-rw-20261023/final-native-gate'
sys.path.insert(0,str(D))
import FinalNativeGate_guard as g

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
c=load(E/'FinalNativeGateV6-caller-template.py','caller_v6')

def stat(pid=12,start=99,rss=3):
    f=['S','1']+['0']*17+[str(start),'0',str(rss)]
    return str(pid)+' (mutable comm) '+' '.join(f)

def read(path):
    parts=path.split('/');pid=int(parts[2]);tid=int(parts[4]) if '/task/' in path else pid
    if path.endswith('/stat'):return stat(tid)
    if path.endswith('/status'):return f'Tgid:\t{pid}\nPid:\t{tid}\n'
    if path.endswith('/children'):return '14'
    raise AssertionError(path)

class ProcTests(unittest.TestCase):
    def proc(self):
        p=g.Proc();p.read=Mock(side_effect=read);p.absent=Mock(return_value=True);return p

    def test_original_optional_esrch_and_enoent(self):
        for error in (ProcessLookupError(3,'original immutable counterexample'),FileNotFoundError(2,'gone')):
            p=self.proc();p.identity=Mock(side_effect=error)
            self.assertIsNone(p.optional(12))
            self.assertEqual(p.events[-1]['errno'],error.errno)
            self.assertTrue(p.events[-1]['independent_absence']['absent'])
            self.assertEqual(p.events[-1]['path'],'/proc/12')

    def test_exact_read_failure_context_and_known_identity(self):
        p=self.proc();p.identity(12)
        def fail(path):
            if path.endswith('/status'):raise ProcessLookupError(3,'status vanished')
            return read(path)
        p.read.side_effect=fail
        self.assertIsNone(p.optional(12));event=p.events[-1]
        self.assertEqual(event['operation'],'read-status');self.assertEqual(event['path'],'/proc/12/status')
        self.assertEqual(event['known_stable_identity'],dict(pid=12,tgid=12,starttime=99))

    def test_original_task_children_esrch_verified(self):
        p=self.proc()
        def fail(path):
            if path.endswith('/children'):raise ProcessLookupError(3,'original task shape')
            return read(path)
        p.read.side_effect=fail
        with patch.object(g.os,'listdir',return_value=['12']):self.assertEqual(p.children(12),set())
        event=p.events[-1];self.assertEqual(event['operation'],'read-task-children')
        self.assertEqual(event['path'],'/proc/12/task/12/children');self.assertEqual(event['tid'],'12')
        self.assertEqual(event['known_stable_identity']['tgid'],12)

    def test_live_unknown_permission_and_other_errno_failclosed(self):
        for error,absence in [(ProcessLookupError(3,'live'),False),(FileNotFoundError(2,'live'),False),
                              (ProcessLookupError(3,'unknown'),None),(PermissionError(13,'denied'),True),
                              (OSError(5,'io'),True),(ProcessLookupError(5,'wrong errno'),True)]:
            p=self.proc();p.absent.return_value=absence;p.read.side_effect=error
            with self.assertRaises(g.GuardError):p.optional(12)
            self.assertEqual(p.events[-1]['errno'],error.errno)
        p=self.proc();p.read.side_effect=ProcessLookupError(3,'gone');p.absent.side_effect=PermissionError(13,'visibility')
        with self.assertRaises(g.GuardError):p.optional(12)
        self.assertIn('error',p.events[-1]['independent_absence'])

    def test_task_absence_false_and_permission_failclosed(self):
        for error,absence in [(ProcessLookupError(3,'live task'),False),(PermissionError(13,'denied'),True)]:
            p=self.proc();p.absent.return_value=absence
            p.read.side_effect=lambda path: (_ for _ in ()).throw(error) if path.endswith('/children') else read(path)
            with patch.object(g.os,'listdir',return_value=['12']),self.assertRaises(g.GuardError):p.children(12)

    def test_malformed_reused_and_tgid_failclosed(self):
        for raw in ('malformed',stat(start=-1),stat(pid=13),stat(rss=-1)):
            p=self.proc();p.read.side_effect=lambda path: raw if path.endswith('/stat') else read(path)
            with self.assertRaises(g.GuardError):p.optional(12)
            self.assertEqual(p.events[-1]['operation'],'parse-identity')
        p=self.proc();p.identity(12);p.read.side_effect=lambda path:stat(start=100) if path.endswith('/stat') else read(path)
        with self.assertRaises(g.GuardError):p.optional(12)
        p=self.proc();p.read.side_effect=lambda path:'Tgid: 13\nPid: 12\n' if path.endswith('/status') else read(path)
        with self.assertRaises(g.GuardError):p.optional(12)

    def test_before_after_envelope_comm_ignored_and_reuse_denied(self):
        p=self.proc();self.assertEqual(p.identity(12)['tgid'],12)
        count=0
        def drift(path):
            nonlocal count
            if path.endswith('/stat'):
                count+=1;return stat(start=99 if count==1 else 100)
            return read(path)
        p=self.proc();p.read.side_effect=drift
        with self.assertRaises(g.GuardError):p.identity(12)
        p=self.proc();p.read.side_effect=lambda path:read(path).replace('mutable comm','exec changed')
        self.assertEqual(p.identity(12)['starttime'],99)

    def test_parent_reuse_after_task_disappearance_is_not_accepted(self):
        p=self.proc();count=0
        def drift(path):
            nonlocal count
            if path=='/proc/12/stat':
                count+=1;return stat(start=99 if count<=2 else 100)
            if path.endswith('/children'):raise ProcessLookupError(3,'task gone')
            return read(path)
        p.read.side_effect=drift
        with patch.object(g.os,'listdir',return_value=['12']),self.assertRaises(g.GuardError):p.children(12)

    def test_tasklist_esrch_collector_vs_retained_descendant(self):
        for pid in (12,14):
            p=self.proc()
            with patch.object(g.os,'listdir',side_effect=ProcessLookupError(3,'task list gone')):
                with self.assertRaises(g.Gone):p.children(pid)
            self.assertEqual(p.events[-1]['operation'],'list-task')
        for root in (True,False):
            p=Mock();p.events=[]
            p.optional.side_effect=lambda pid:dict(pid=pid,ppid=12,starttime=99,rss_bytes=100,tgid=pid)
            p.children.side_effect=lambda pid: (_ for _ in ()).throw(g.Gone('verified')) if (pid==12 if root else pid==14) else set()
            guard=g.Guard(proc=p,pid=12,notify=Mock());guard.owned={12:99,14:99}
            if root:
                with self.assertRaisesRegex(g.GuardError,'collector disappeared'):guard.sample()
            else:
                guard.sample();self.assertEqual(guard.samples[-1]['rss_bytes'],200);self.assertIn(14,guard.owned)

    def test_retained_exec_reparent_group_change_and_collector_absent(self):
        p=Mock();p.optional.side_effect=lambda pid:dict(pid=pid,ppid=777,starttime=99,rss_bytes=100,tgid=pid)
        p.children.return_value=set();guard=g.Guard(proc=p,pid=12,notify=Mock());guard.owned={12:99,14:99}
        guard.sample();self.assertEqual(guard.samples[-1]['processes'],[12,14])
        p.optional.return_value=None;p.optional.side_effect=None
        with self.assertRaisesRegex(g.GuardError,'collector disappeared'):guard.sample()

    def test_cancel_pidfd_precedes_identity_and_no_unverified_signal(self):
        p=self.proc();trace=[]
        with patch.object(g.os,'pidfd_open',side_effect=lambda pid:trace.append('pidfd') or 9,create=True),patch.object(g.os,'close'),patch.object(g.signal,'pidfd_send_signal',side_effect=lambda *x:trace.append('signal'),create=True):
            original=p.optional;p.optional=lambda pid:trace.append('identity') or original(pid)
            self.assertEqual(p.cancel(12,99),'verified-owned-signalled');self.assertEqual(trace,['pidfd','identity','signal'])
            trace.clear();self.assertEqual(p.cancel(12,100),'reused-not-signalled');self.assertEqual(trace,['pidfd','identity'])
        p=self.proc();p.absent.return_value=False
        with patch.object(g.os,'pidfd_open',side_effect=ProcessLookupError(3,'unknown'),create=True),self.assertRaises(g.GuardError):p.cancel(12,99)

    def test_malformed_children_and_task_list_context(self):
        p=self.proc();p.read.side_effect=lambda path:'oops' if path.endswith('/children') else read(path)
        with patch.object(g.os,'listdir',return_value=['12']),self.assertRaises(g.GuardError):p.children(12)
        self.assertEqual(p.events[-1]['operation'],'parse-task-children')
        p=self.proc()
        with patch.object(g.os,'listdir',return_value=['not-a-tid']),self.assertRaises(g.GuardError):p.children(12)
        self.assertEqual(p.events[-1]['operation'],'parse-task-list')

    def test_tasklist_live_or_unknown_visibility_fails_closed(self):
        for absent in (False,None):
            p=self.proc();p.absent.return_value=absent
            with patch.object(g.os,'listdir',side_effect=ProcessLookupError(3,'task list failed')),self.assertRaises(g.GuardError):p.children(12)
            self.assertEqual(p.events[-1]['path'],'/proc/12/task')

    def test_task_disappears_between_children_read_and_envelope(self):
        p=self.proc();done=False
        def vanish(path):
            nonlocal done
            if path.endswith('/children'):done=True;return '14'
            if '/task/' in path and done:raise ProcessLookupError(3,'post-read disappeared')
            return read(path)
        p.read.side_effect=vanish
        with patch.object(g.os,'listdir',return_value=['12']):self.assertEqual(p.children(12),set())
        self.assertEqual(p.events[-1]['operation'],'read-stat')



def row(pid=20,command='python3',**kw):
    return dict(pid=pid,ppid=kw.get('ppid',10),uid=kw.get('uid',501),pgid=kw.get('pgid',20),
                start=kw.get('start','Sun Oct 25 12:00:00 2026'),rss_bytes=kw.get('rss_bytes',100),command=command)

class CallerTests(unittest.TestCase):
    def collector(self,polls,rows=None):
        child=Mock(pid=20);child.poll.side_effect=polls;child.wait.return_value=78
        scan=Mock(return_value={20:row()} if rows is None else rows)
        return c.Collector(child,scan,lambda:0,clock=lambda:0,parent_pid=10,uid=501)

    def test_defunct_already_exited_reaped_before_snapshot(self):
        x=self.collector([78]);self.assertFalse(x.sample());x.snapshot.assert_not_called()
        self.assertEqual(x.rc,78);self.assertTrue(x.reaped);x.child.kill.assert_not_called()

    def test_same_birth_defunct_and_exec_comm_ignored(self):
        x=self.collector([None,None,None,None])
        self.assertTrue(x.sample());x.snapshot.return_value={20:row(command='<defunct>',rss_bytes=0)}
        self.assertTrue(x.sample());self.assertEqual(len(x.samples),2)
        y=self.collector([None,None,None,None]);y.sample();y.snapshot.return_value={20:row(command='/usr/bin/non-native-fixture')}
        self.assertTrue(y.sample())

    def test_exit_between_poll_and_scan_reaps_before_liveness_check(self):
        x=self.collector([None,78],{20:row(start='reused after reap',uid=999)})
        self.assertFalse(x.sample());self.assertEqual(x.rc,78);self.assertTrue(x.reaped)
        self.assertTrue(x.samples[-1]['root_already_exited']);self.assertEqual(x.samples[-1]['processes'],[])

    def test_exit_between_poll_and_missing_scan(self):
        x=self.collector([None,78],{});self.assertFalse(x.sample());self.assertEqual(x.rc,78)
        y=self.collector([None,None],{})
        with self.assertRaisesRegex(ValueError,'visibility unknown'):y.sample()

    def test_pidreuse_and_live_hard_mismatch(self):
        for key,value in [('start','new birth'),('ppid',11),('uid',502),('pgid',21)]:
            x=self.collector([None,None,None,None]);x.sample();x.snapshot.return_value={20:row(**{key:value})}
            with self.assertRaisesRegex(ValueError,'hard identity drift'):x.sample()
            x.child.kill.assert_not_called()
        x=self.collector([None,None],{20:row(uid=999)})
        with self.assertRaisesRegex(ValueError,'hard identity mismatch'):x.sample()

    def test_actual_rc_persisted_if_reap_errors_then_finish(self):
        x=self.collector([78,78]);x.child.wait.side_effect=[TimeoutError('reap fault'),78]
        with self.assertRaises(TimeoutError):x.sample()
        self.assertEqual(x.rc,78);x.finish();self.assertEqual(x.rc,78);self.assertTrue(x.reaped)

    def test_permission_failure_not_empty_snapshot_and_final_rc(self):
        x=self.collector([None,78]);x.snapshot.side_effect=PermissionError('ps denied')
        with self.assertRaises(PermissionError):x.sample()
        x.finish();self.assertEqual(x.rc,78);self.assertEqual(x.samples,[]);x.child.kill.assert_not_called()

    def test_control_error_retained_safe_owned_reap(self):
        x=self.collector([None,None,None,None,78]);x.sample();x.child.kill.side_effect=PermissionError('control denied')
        x.finish();self.assertEqual(x.rc,78);self.assertTrue(x.reaped)
        self.assertTrue(x.control_attempted);self.assertIn('control denied',str(x.errors))

    def test_cleanup_mismatch_never_signals_and_retains_unreaped(self):
        x=self.collector([None,None,None,None,None]);x.sample();x.snapshot.return_value={20:row(start='new birth')}
        x.child.wait.side_effect=TimeoutError('still unresolved');x.finish()
        x.child.kill.assert_not_called();self.assertFalse(x.reaped);self.assertIsNone(x.rc)
        self.assertIn('identity unresolved',str(x.errors));self.assertIn('reap unresolved',str(x.errors))

    def test_exit_during_cleanup_does_not_signal(self):
        x=self.collector([None,None,None,78]);x.sample();x.finish()
        x.child.kill.assert_not_called();self.assertTrue(x.reaped);self.assertFalse(x.control_needed)

    def test_metrics_limits_and_descriptive_zero(self):
        x=self.collector([None,None],{20:row(rss_bytes=512*2**20)})
        with self.assertRaises(MemoryError):x.sample()
        self.assertEqual(len(x.samples),1)
        x=self.collector([None,None]);x.output_bytes=lambda:4*2**20+1
        with self.assertRaises(ValueError):x.sample()
        x=self.collector([None,None]);x.clock=lambda:136
        with self.assertRaises(TimeoutError):x.sample()
        with self.assertRaises(ValueError):c.parse_ps('bad ps row')

    def test_exact_one_exclusive_charge_and_disabled_main_no_ssh(self):
        with tempfile.TemporaryDirectory(prefix='FinalNativeGateV6-charge-') as tmp:
            p=Path(tmp)/'charge.json';c.exclusive_charge(p,{'sha256':'fixture'})
            with self.assertRaises(FileExistsError):c.exclusive_charge(p,{'sha256':'fixture'})
            self.assertEqual(json.loads(p.read_text())['main_precharged'],1)
        with patch('subprocess.Popen',side_effect=AssertionError('no actual launch')):
            self.assertEqual(c.main(),78)

    def test_safe_owned_control_success_and_reap(self):
        x=self.collector([None,None,None,None,None]);x.sample();x.finish()
        x.child.kill.assert_called_once();self.assertTrue(x.reaped);self.assertEqual(x.rc,78)
        self.assertEqual(x.errors,[])

    def test_retained_child_visibility_missing_is_partial_failure(self):
        x=self.collector([None,None,None,None],{20:row(),21:row(pid=21,ppid=20)})
        x.sample();x.snapshot.return_value={20:row()}
        with self.assertRaisesRegex(ValueError,'descendants visibility unresolved'):x.sample()
        self.assertEqual(x.samples[-1]['missing_retained'],[21]);self.assertFalse(x.samples[-1]['metrics_complete'])

    def test_default_future_allocation_unavailable(self):
        with patch('subprocess.Popen',side_effect=AssertionError('no launch')):
            with self.assertRaisesRegex(ValueError,'no future caller allocation'):c.future_precharge('unused')
        text=(E/'FinalNativeGateV6-caller-template.py').read_text()
        self.assertNotIn('subprocess.Popen(',text);self.assertNotIn('killpg(',text)


    def test_valid_kernel_metadata_and_uid_zero_are_not_permission_errors(self):
        rows=c.parse_ps('0 0 0 0 0 Sun Oct 25 12:00:00 2026 kernel_task\n1 0 0 1 10 Sun Oct 25 12:00:00 2026 launchd')
        self.assertEqual(rows[1]['uid'],0)
        self.assertEqual(c.identity(row(uid=0))[2],0)

    def test_exact_owned_reaped_sampler_is_charged_without_retaining_live_ownership(self):
        class Sample(dict):pass
        data=Sample({20:row(),21:row(pid=21,ppid=10)});data.reaped_sampler=21
        x=self.collector([None,None,None,None],data);x.sample()
        self.assertNotIn(21,x.owned)
        self.assertEqual(x.samples[-1]['rss_bytes'],200)
        x.snapshot.return_value={20:row()};self.assertTrue(x.sample())


if __name__=='__main__':unittest.main(verbosity=2)
