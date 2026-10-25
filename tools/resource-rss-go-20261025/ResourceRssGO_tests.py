"""New focused resident-guard and changed-boundary tests; historical suites reused."""
import ast
import copy
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import ResourceRssGO_guard as g
import ResourceRssGO_host as h
import ResourceRssGO_local as local
import ResourceRssGO_sources as sources
import ResourceRssGO_audit as audit
from ResourceRssGO_fixtures import fixture, kernel

class Synthetic:
    def __init__(self):
        self.rows={1:dict(pid=1,ppid=0,starttime=10,rss_bytes=100,vsize=2**48)}
        self.edges={1:set()}
        self.cancelled=[]
    def optional(self,pid):
        row=self.rows.get(pid)
        if isinstance(row,Exception):raise row
        return row
    def children(self,pid):return self.edges.get(pid,set())
    def cancel(self,pid,start):
        row=self.optional(pid)
        if row is None:return 'disappeared'
        if row['starttime']!=start:return 'reused-not-signalled'
        self.cancelled.append(pid);return 'verified-owned-signalled'
    def child(self,pid=2,rss=100):
        self.rows[pid]=dict(pid=pid,ppid=1,starttime=pid*10,rss_bytes=rss)
        self.edges[1].add(pid)

class ResourceRssGOTests(unittest.TestCase):
    def test_large_virtual_small_resident_and_dedup(self):
        p=Synthetic();p.child();p.edges[2]={2}
        guard=g.Guard(p,1,lambda:None);guard.sample()
        self.assertEqual(guard.peak,200)
        self.assertEqual(len(guard.samples[0]['processes']),2)
        self.assertEqual(p.rows[1]['vsize'],2**48)

    def test_aggregate_breach_reuse_and_unknown_visibility(self):
        p=Synthetic();p.child(rss=g.BUDGET)
        guard=g.Guard(p,1,lambda:None)
        with self.assertRaisesRegex(g.GuardError,'aggregate'):guard.sample()
        p.rows[2]['rss_bytes']=1;guard.sample()
        p.rows[2]['starttime']+=1
        with self.assertRaisesRegex(g.GuardError,'reuse'):guard.sample()
        for failure in (PermissionError(13,'unknown'),g.GuardError('unknown live-child visibility')):
            p=Synthetic();p.child();p.rows[2]=failure
            with self.assertRaises((PermissionError,g.GuardError)):g.Guard(p,1,lambda:None).sample()
        p=Synthetic();p.child();p.rows[2]['ppid']=99
        with self.assertRaisesRegex(g.GuardError,'lineage'):g.Guard(p,1,lambda:None).sample()

    def test_disappearance_and_only_owned_cancellation(self):
        p=Synthetic();p.child();guard=g.Guard(p,1,lambda:None);guard.sample()
        p.rows.pop(2);guard.sample()
        p.child(3);guard.sample();p.rows[3]['starttime']+=1
        p.rows[99]=dict(pid=99,ppid=0,starttime=99,rss_bytes=5)
        guard.cancel_owned()
        self.assertEqual(p.cancelled,[])
        # Earlier reused PID remains fatal; don't reset history to bypass it.
        with self.assertRaisesRegex(g.GuardError,'reuse'):guard.sample()
        other=g.Guard(Synthetic(),1,lambda:None);other.proc.child(4);other.sample();other.cancel_owned()
        self.assertEqual(other.proc.cancelled,[4]);self.assertNotIn(1,other.proc.cancelled)

    def test_pidfd_identity_checked_before_signal(self):
        proc=g.Proc();row=dict(starttime=5)
        with patch.object(os,'pidfd_open',return_value=123,create=True),patch.object(os,'close') as close,patch.object(signal,'pidfd_send_signal',create=True) as kill,patch.object(proc,'optional',return_value=row):
            self.assertEqual(proc.cancel(9,6),'reused-not-signalled');kill.assert_not_called()
            self.assertEqual(proc.cancel(9,5),'verified-owned-signalled');kill.assert_called_once_with(123,signal.SIGKILL)
            self.assertEqual(close.call_count,2)

    def test_proc_fields_disappeared_task_and_permission(self):
        proc=g.Proc()
        tail=['S','0']+['0']*17+['123',str(2**48),'7']
        reads={'/proc/1/stat':'1 (name with ) parens) '+' '.join(tail),'/proc/1/status':'Pid: 1\nTgid: 1\n','/proc/1/task/1/children':'2 2\n'}
        with patch.object(proc,'read',side_effect=lambda path:reads[path]):
            self.assertEqual(proc.identity(1)['rss_bytes'],7*os.sysconf('SC_PAGE_SIZE'))
            with patch.object(os,'listdir',return_value=['1']):self.assertEqual(proc.children(1),{2})
        with patch.object(proc,'identity',side_effect=FileNotFoundError),patch.object(proc,'absent',return_value=True):self.assertIsNone(proc.optional(2))
        with patch.object(proc,'identity',side_effect=FileNotFoundError),patch.object(proc,'absent',return_value=False),self.assertRaisesRegex(g.GuardError,'visibility'):proc.optional(2)
        with patch.object(proc,'identity',side_effect=PermissionError),self.assertRaises(PermissionError):proc.optional(2)

    def test_monitor_lifecycle_bounds_fail_closed(self):
        guard=g.Guard(Synthetic(),1,lambda:None);guard.start()
        thread=guard.thread;self.assertTrue(thread.is_alive());guard.check();guard.check()
        receipt=guard.finish();self.assertFalse(thread.is_alive());self.assertGreaterEqual(len(receipt['samples']),2)
        self.assertLess(receipt['started'],receipt['samples'][0]['monotonic'])
        p=Synthetic();p.child(rss=g.BUDGET);notified=[]
        guard=g.Guard(p,1,lambda:notified.append(True))
        with self.assertRaises(g.GuardError):guard.start()
        guard.finish(True);self.assertTrue(notified);self.assertEqual(p.cancelled,[2,2])
        guard=g.Guard(Synthetic(),1,lambda:None)
        with patch.object(g,'MAX_SAMPLES',0),self.assertRaisesRegex(g.GuardError,'sample record limit'):guard.sample()

    def test_inherited_limits_unchanged_tiny_child_no_setters(self):
        initial=g.inherited_limits()
        child=subprocess.run([sys.executable,'-I','-B','-c','import resource,json;print(json.dumps({n:list(resource.getrlimit(getattr(resource,n))) for n in sorted(dir(resource)) if n.startswith("RLIMIT_")}))'],capture_output=True,text=True,check=True,timeout=5)
        self.assertEqual(json.loads(child.stdout),initial);self.assertEqual(g.inherited_limits(),initial)
        unlimited={name:[resource.RLIM_INFINITY]*2 for name in ('RLIMIT_AS','RLIMIT_DATA')};g.check_limits(unlimited,unlimited)
        with self.assertRaisesRegex(g.GuardError,'restriction'):g.check_limits(dict(unlimited,RLIMIT_AS=[1,1]))
        with self.assertRaisesRegex(g.GuardError,'changed'):g.check_limits(unlimited,{})
        host_source=Path(h.__file__).read_text()
        self.assertLess(host_source.index('ACTIVE_GUARD.start()'),host_source.index('result=main()'))
        self.assertLess(host_source.index('result=main()'),host_source.index('ACTIVE_GUARD.finish(failed=failed)'))
        for p in Path(__file__).parent.glob('*.py'):
            tree=ast.parse(p.read_text())
            self.assertFalse(any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in ('setrlimit','prlimit') for n in ast.walk(tree)))

    def test_literal_env_strict_source_unit_control_and_deny(self):
        expected=local.env(1000);argv=h.scope_argv(dict(env=expected))
        self.assertEqual(argv[:14],['/usr/bin/systemd-run','--user','--scope','--unit='+h.UNIT,'-p','MemoryHigh=3G','-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/env','-i'])
        self.assertEqual(argv[21:],['/usr/bin/python3','-I','-B',h.STAGE+'/ResourceRssGO_host.py','go'])
        dirty=dict(expected,INVOCATION_ID='dirty',LANG='dirty')
        child=subprocess.run(argv[12:21]+['/usr/bin/env'],env=dirty,check=True,capture_output=True,text=True,timeout=5)
        observed=dict(line.split('=',1) for line in child.stdout.splitlines());self.assertEqual(observed,expected)
        with patch.dict(os.environ,observed,clear=True):h.verify_environment(expected)
        with patch.dict(os.environ,dirty,clear=True),self.assertRaises(ValueError):h.verify_environment(expected)
        denied=dict(decision=dict(allowed=False))
        self.assertFalse(h.flow(lambda:denied,lambda:self.fail('scope'))['scope_created'])
        self.assertIsNone(h.go_flow(denied,lambda:self.fail('marker'))['marker_exit'])
        with tempfile.TemporaryDirectory() as t,patch.object(h,'HERE',Path(t)),patch.object(h,'STAGE',t):
            p=Path(t)/'x';p.write_text('x');m=dict(epoch=h.EPOCH,stage=t,env=expected,mode=h.MODE,files={'x':h.filepin(p)})
            m['scope_argv']=h.scope_argv(m)
            with self.assertRaisesRegex(ValueError,'argv'):h.verify(dict(m,scope_argv=[]))
            p.write_text('changed')
            with self.assertRaisesRegex(ValueError,'source drift'):h.verify(m)
        values={'memory.high':str(h.EXPECTED['high']),'memory.max':str(h.EXPECTED['cap']),'memory.swap.max':'0','memory.swap.current':'0','pids.max':'64','pids.current':'1','memory.current':'100','memory.peak':'200','memory.events':'low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0\n'}
        self.assertTrue(h.check_controls(dict(values=values)))
        for key,val in [('memory.swap.current','1'),('memory.peak',str(5*2**30)),('pids.max','65')]:
            with self.assertRaises(ValueError):h.check_controls(dict(values=dict(values,**{key:val})))
        with kernel(fixture()),patch.object(h.adapter,'UNIT','wrong-unit'):
            self.assertFalse(h.adapter.read_only_admission(phase='inside-scope')['decision']['allowed'])
        with kernel(fixture()) as files:
            self.assertTrue(h.adapter.read_only_admission(phase='inside-scope')['decision']['allowed'])
            files['/proc/self/status']=PermissionError(13,'denied')
            self.assertFalse(h.adapter.read_only_admission(phase='inside-scope')['decision']['allowed'])

    def test_changed_collector_ordered_replay(self):
        for phase,fault in [('prospective',False),('inside-scope',False),('prospective',True)]:
            with tempfile.TemporaryDirectory() as t,patch.object(h,'HERE',Path(t)):
                with kernel(fixture()) as files:
                    if fault:files['/proc/self/status']=PermissionError(13,'synthetic denied')
                    report=h.collect(phase)
                self.assertEqual(report['decision']['allowed'],not fault)
                cap=Path(t)/'capture';pins={p.name:dict(name=p.name,**h.filepin(p)) for p in cap.iterdir()}
                (cap/'export-receipt.json').write_text(json.dumps(dict(host_files=pins)))
                with patch.object(audit,'OUT',cap):self.assertEqual(audit.replay(phase)['allowed'],not fault)

if __name__=='__main__':unittest.main(verbosity=2)
