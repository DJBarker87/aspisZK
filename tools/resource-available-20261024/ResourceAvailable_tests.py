"""Focused policy/observer tests, synthetic only. No live reads or consumers."""
import copy
import contextlib
import io
import unittest
from pathlib import Path
from unittest.mock import patch
import ResourceAvailable_candidate as c
import ResourceAvailable_go as go
G=c.GIB


def node(path='/cg/a',current=G,cap=8*G,owner='/cg',subtree=False):
    return dict(path=path,parent=path.rsplit('/',1)[0],root=False,enabled=True,
        owner=owner,subtree_memory=subtree,populated=True,procs=[],threads=[],identities=[],
        type='domain',domain=path,procs_errno=0,controllers=['memory','pids'],
        pids_enabled=False,subtree_pids=False,tasks_max=None,pids_current=None,
        current=current,cap=cap,high=None,swap_max=0,swap_current=0,
        stat={k:0 for k in c.REQUIRED})


def fixture(*nodes):
    nodes=list(nodes) or [node()]
    root=dict(path='/cg',parent=None,root=True,enabled=False,owner='/cg',
        subtree_memory=True,procs=[],threads=[],identities=[],type='root-special-domain',
        domain='/cg',procs_errno=0,controllers=['memory','pids'],pids_enabled=False,
        subtree_pids=False,tasks_max=None,pids_current=None)
    top=sum(r['current'] for r in nodes if r['owner']=='/cg')
    return dict(rows=[root,*nodes],meminfo=dict(MemTotal=100*G,MemFree=100*G-top-G,
        MemAvailable=80*G,**{'Active(file)':2*G,'SReclaimable':4*G,'KReclaimable':5*G}))


def legacy(s,q):
    a=c.observe(s)
    return dict(cgroups=[dict(path=p,charged_bytes=next(r['cap'] for r in s['rows'] if r['path']==p)) for p in a['frontier']],
        projected_reserved_bytes=a['bounded_reserved_bytes']+q,allowed=True,reserve_check=True,
        process_visibility='processes',service_visibility='services',docker_visibility=[])


def evaluate(s,q=4*G,after=None,old=None,**kw):
    return go.evaluate(legacy(s,q) if old is None else old,s,s if after is None else after,q,
        phase=kw.pop('phase','prospective'),**kw)


def scope(high=6*G,cap=8*G,ancestor=False):
    s=fixture(node('/cg/job.scope',cap=cap))
    root,row=s['rows'];root.update(path='/sys/fs/cgroup',owner='/sys/fs/cgroup',domain='/sys/fs/cgroup',subtree_pids=True)
    row.update(path='/sys/fs/cgroup/job.scope',parent=root['path'],owner=root['path'],domain='/sys/fs/cgroup/job.scope',
        high=high,procs=[42],threads=[42],identities=[dict(tid=42,tgid=42,starttime=123)],
        pids_enabled=True,pids_current=1,tasks_max=64)
    if ancestor:
        p=node('/sys/fs/cgroup/parent',cap=12*G,owner=root['path'],subtree=True)
        p.update(high=10*G,subtree_pids=True,pids_enabled=True,pids_current=1,tasks_max=128)
        row.update(path=p['path']+'/job.scope',parent=p['path'],owner=p['path'],domain=p['path']+'/job.scope')
        s['rows'].insert(1,p)
    s['self_observation']=dict(pid=42,starttime=123,path=row['path'],unified_path=row['path'][len('/sys/fs/cgroup'):])
    return s,dict(high=high,cap=cap,swap_max=0,tasks_max=64)


class ResourceAvailableTests(unittest.TestCase):
    def test_fixed_formula(self):
        d=evaluate(fixture());self.assertTrue(d['allowed'],d)
        self.assertEqual(d['adjusted_available_bytes'],74*G)
        self.assertEqual(d['required_bytes'],19*G)

    def test_strict_frontier_equality(self):
        s=fixture(node(cap=51*G));self.assertFalse(evaluate(s)['allowed'])
        s['rows'][1]['cap']-=1;self.assertTrue(evaluate(s)['allowed'])

    def test_strict_adjusted_and_available_equality(self):
        s=fixture();s['meminfo']['MemAvailable']=25*G
        self.assertFalse(evaluate(s)['allowed'])
        s['meminfo']['MemAvailable']+=1;self.assertTrue(evaluate(s)['allowed'])
        s['meminfo']['MemAvailable']=6*G;self.assertFalse(evaluate(s)['allowed'])

    def test_each_reserve_component_monotonic(self):
        s=fixture();base=evaluate(s)
        for key in ('Active(file)','KReclaimable','MemFree','MemAvailable','SReclaimable','B','Q'):
            b=copy.deepcopy(s);q=4*G
            if key=='MemFree':b['meminfo'][key]-=1024
            elif key=='MemAvailable':b['meminfo'][key]-=1024
            elif key=='SReclaimable':b['meminfo'][key]-=2048
            elif key=='B':b['rows'][1]['cap']+=1024
            elif key=='Q':q+=1024
            else:b['meminfo'][key]+=1024
            d=evaluate(b,q);self.assertEqual(d['margin_bytes'],base['margin_bytes']-1024,key)

    def test_pair_envelope_mixed_extrema(self):
        s=fixture();b=copy.deepcopy(s)
        b['meminfo']['MemAvailable']-=100;b['meminfo']['Active(file)']+=200
        b['meminfo']['KReclaimable']+=300;b['meminfo']['MemFree']-=400
        d=evaluate(s,after=b)
        self.assertEqual(d['adjusted_available_bytes'],evaluate(s)['adjusted_available_bytes']-1000)
        self.assertEqual(d['adjusted_available_bytes'],evaluate(b,after=s)['adjusted_available_bytes'])

    def test_checked_arithmetic(self):
        self.assertRaises(ValueError,c.add,[c.U64,1])
        for value in (-1,True,1.0,c.U64+1,'1'):
            self.assertRaises(ValueError,c.uint,value)
        s=fixture();s['meminfo']['MemAvailable']=1
        self.assertIn('error',evaluate(s))
        self.assertIn('error',evaluate(fixture(),q=c.U64))
        s=fixture();s['meminfo'].update(MemTotal=c.U64,MemFree=0,MemAvailable=c.U64,
            **{'Active(file)':c.U64,'KReclaimable':c.U64,'SReclaimable':0})
        self.assertIn('error',evaluate(s))

    def test_global_errors(self):
        good=fixture();lg=legacy(good,4*G)
        for key in ('MemTotal','MemFree','MemAvailable','Active(file)','SReclaimable','KReclaimable'):
            for value in (None,-1,c.U64+1,True):
                s=copy.deepcopy(good)
                if value is None:del s['meminfo'][key]
                else:s['meminfo'][key]=value
                self.assertIn('error',evaluate(s,old=lg),(key,value))
            if key!='MemTotal':
                s=copy.deepcopy(good);s['meminfo'][key]=101*G
                self.assertIn('error',evaluate(s,old=lg),key)
        s=fixture();s['meminfo']['KReclaimable']=0;self.assertIn('error',evaluate(s,old=lg))
        s=fixture();s['meminfo']['MemFree']=100*G;self.assertIn('error',evaluate(s,old=lg))

    def test_negative_and_overlap_diagnostics_only(self):
        s=fixture(node(current=G,cap=8*G,subtree=True),node('/cg/a/b',current=G,cap=4*G,owner='/cg/a'))
        base=evaluate(s)
        s['rows'][2]['stat'].update(anon=10,slab_reclaimable=20,active_file=30,kernel=40)
        s['rows'][1]['stat']['inactive_file']=5*G
        d=evaluate(s);self.assertTrue(d['allowed'],d)
        diag=d['before_observation']['diagnostics'][0]
        self.assertEqual(diag['exclusive_stat']['anon'],-10)
        self.assertTrue(diag['type_lru_overlap'])
        self.assertEqual(base['adjusted_available_bytes'],d['adjusted_available_bytes'])
        # Even signed exclusive current is unused. Root R remains raw checked.
        s['rows'][2]['current']+=1
        self.assertLess(c.observe(s)['diagnostics'][0]['exclusive_current'],0)
        self.assertTrue(evaluate(s)['allowed'])

    def test_raw_stat_errors_not_ignored(self):
        s=fixture();lg=legacy(s,4*G)
        for key in c.REQUIRED+('extra_unused',):
            b=copy.deepcopy(s);b['rows'][1]['stat'][key]=-1
            self.assertIn('error',evaluate(b,old=lg),key)
        for key in c.REQUIRED:
            b=copy.deepcopy(s);del b['rows'][1]['stat'][key]
            self.assertIn('error',evaluate(b,old=lg),key)
        for raw in ('anon -1','anon 1\nanon 2','anon x','anon 18446744073709551616'):
            self.assertRaises(ValueError,c.pairs,raw)

    def test_visibility_and_nonreserve_errors(self):
        s=fixture();lg=legacy(s,4*G)
        for key in ('error','visibility_error'):
            b=dict(lg);b[key]='failure';self.assertFalse(evaluate(s,old=b)['allowed'])
        for key in lg:
            b=dict(lg);del b[key];self.assertFalse(evaluate(s,old=b)['allowed'],key)
        b=dict(lg,allowed=False,reserve_check=True)
        self.assertFalse(evaluate(s,old=b)['allowed'])
        b=dict(lg,allowed=False,reserve_check=False)
        self.assertTrue(evaluate(s,old=b)['allowed'])
        b=dict(lg,projected_reserved_bytes=1)
        self.assertIn('error',evaluate(s,old=b))
        b=dict(lg,cgroups=[]);self.assertIn('error',evaluate(s,old=b))

    def test_tree_pid_controller_and_cap_errors(self):
        s=fixture();lg=legacy(s,4*G)
        for key,value in (('current',9*G),('swap_current',1),('owner','/bad'),('parent','/bad'),
                ('enabled',False),('threads',[42]),('procs',[42]),('type','invalid'),('populated',False)):
            b=copy.deepcopy(s);b['rows'][1][key]=value
            if key=='populated':b['rows'][1]['threads']=[42]
            self.assertIn('error',evaluate(b,old=lg),(key,value))
        b=copy.deepcopy(s);b['rows'].append(copy.deepcopy(b['rows'][1]));self.assertIn('error',evaluate(b,old=lg))
        b=copy.deepcopy(s);b['rows'][1]['high']=7*G
        self.assertIn('error',evaluate(s,after=b))

    def test_scope_once_both_allowed_sizes_and_ancestor(self):
        for high,cap in ((3*G,4*G),(6*G,8*G)):
            for ancestor in (False,True):
                s,e=scope(high,cap,ancestor)
                d=evaluate(s,q=0,phase='inside-scope',expected=e)
                self.assertTrue(d['allowed'],d)
                self.assertEqual(d['projected_reserved_bytes'],12*G if ancestor else cap)

    def test_phase_and_binding_errors(self):
        s,e=scope();lg=legacy(s,0)
        for phase,q in (('unknown',0),('prospective',0),('inside-scope',1)):
            self.assertFalse(go.evaluate(lg,s,s,q,phase=phase,expected=e)['allowed'])
        for key,value in (('pid',43),('starttime',124),('path','/sys/fs/cgroup/fake.scope'),('unified_path','/x/../job.scope')):
            b=copy.deepcopy(s);b['self_observation'][key]=value
            self.assertIn('error',evaluate(b,q=0,old=lg,phase='inside-scope',expected=e))
        for key,value in (('cap',7*G),('high',5*G),('swap_max',1),('swap_current',1),('tasks_max',63),('pids_enabled',False),('populated',False)):
            b=copy.deepcopy(s);b['rows'][-1][key]=value
            self.assertFalse(evaluate(b,q=0,old=lg,phase='inside-scope',expected=e)['allowed'])
        for expected in (None,{},dict(e,extra=1),dict(e,tasks_max=65)):
            self.assertFalse(evaluate(s,q=0,phase='inside-scope',expected=expected)['allowed'])
        for key in ('cap','high','tasks_max'):
            b,e=scope(ancestor=True);lg=legacy(b,0);b['rows'][1][key]=1
            self.assertIn('error',evaluate(b,q=0,old=lg,phase='inside-scope',expected=e))
        b,e=scope();after=copy.deepcopy(b);after['self_observation']['starttime']+=1
        self.assertIn('error',evaluate(b,q=0,after=after,phase='inside-scope',expected=e))

    def test_raw_global_parser_and_delegation(self):
        for raw in ('MemTotal: 1 kB\nMemTotal: 2 kB', 'Unused: -1',
                    'MemAvailable: 1 MB', 'Unused: 18446744073709551616',
                    'Unused: not-a-number'):
            with patch.object(Path,'read_text',return_value=raw):
                self.assertRaises(ValueError,c.scan)
        s=fixture();lg=legacy(s,4*G)
        for key,value in (('controllers',[]),('subtree_memory',False)):
            b=copy.deepcopy(s);b['rows'][0][key]=value
            self.assertIn('error',evaluate(b,old=lg))

    def test_live_disabled_and_source_read_errors(self):
        self.assertRaises(RuntimeError,go.read_only_admission,phase='prospective',additional_bytes=G)
        for exc in (PermissionError(13,'denied'),FileNotFoundError(2,'missing')):
            with patch.object(Path,'read_text',side_effect=exc):self.assertRaises(type(exc),c.scan)


def run():
    stream=io.StringIO()
    result=unittest.TextTestRunner(verbosity=2,stream=stream).run(unittest.defaultTestLoader.loadTestsFromTestCase(ResourceAvailableTests))
    import sys
    sys.stderr.write(stream.getvalue())
    assert result.wasSuccessful()
    return dict(tests=result.testsRun,synthetic=True)
