"""Focused synthetic delta tests; no historical suite relabelled as new."""
import copy
import contextlib
import json
import sys
import types
import unittest
from unittest.mock import patch
import ResourceHierarchy_candidate as c
import ResourceHierarchy_go as go
from ResourceHierarchy_objects import BASE

def run(objects, measured):
    with patch.dict(sys.modules,resource_slab_candidate=c):
        t=types.ModuleType('ResourceHierarchy_fixture')
        exec(compile(objects.read(BASE+'baseline/test_resource_slab.py'),'immutable-fixture','exec'),t.__dict__)
    old=objects.run(BASE+'ResourceStat_go.py')
    with patch.dict(sys.modules,go_api=go,test_resource_slab=t):
        g=types.ModuleType('ResourceHierarchy_scope_fixture')
        exec(compile(objects.read(BASE+'baseline/test_go_api.py'),'immutable-scope-fixture','exec'),g.__dict__)
    def evaluate(s,after=None,legacy=None,q=4*c.GIB,phase='prospective',expected=None):
        return go.evaluate(t.legacy(s,q) if legacy is None else legacy,s,s if after is None else after,q,phase=phase,expected=expected)
    class ResourceHierarchyTests(unittest.TestCase):
        def test_each_component_negative_and_signed_subset(self):
            for key in c.REQUIRED:
                with self.subTest(key=key):
                    s=t.fixture(t.node('/cg/a',200,subtree=True),t.node('/cg/a/b',100,owner='/cg/a'))
                    # Parent E=-1 for chosen field; child internally valid.
                    s['rows'][2]['stat'][key]=1
                    if key.startswith('slab_'):s['rows'][2]['stat']['kernel']=1
                    if key=='kernel':s['rows'][2]['stat']['slab_reclaimable']=1
                    a=c.accounting(s);d=a['exclusive'][0]
                    self.assertLess(d['exclusive_stat'][key],0)
                    self.assertGreater(d['negative_debt'],0)
                    self.assertEqual(d['conservative_charge'],max(d['exclusive_current'],d['positive_sum'])+d['negative_debt'])
                    self.assertEqual(d['reserve'],d['conservative_charge'])
                    self.assertEqual(d['half_slab_credit'],0)
                    self.assertEqual(d['inactive_file_credit'],0)

        def test_signed_slab_kernel_contradiction_still_denies(self):
            s=t.fixture(t.node('/cg/a',200,subtree=True),t.node('/cg/a/b',100,owner='/cg/a',kernel=1))
            # E[kernel]=-1 and sum E[slab]=0 contradict the signed subset rule.
            self.assertRaisesRegex(ValueError,'slab exceeds exclusive kernel',c.accounting,s)
            s['rows'][2]['stat'].update(kernel=0,slab_reclaimable=1)
            s['rows'][1]['stat']['slab_unreclaimable']=2
            # Negative reclaimable does not exempt a positive subset sum > kernel.
            self.assertRaisesRegex(ValueError,'slab exceeds exclusive kernel',c.accounting,s)

        def test_debt_and_charge_checked_overflow(self):
            for mode in ('debt','charge','childsum','positiveSum'):
                s=t.fixture(t.node('/cg/a',200,subtree=True),t.node('/cg/a/b',100,owner='/cg/a'))
                if mode in ('debt','charge'):
                    s['rows'][2]['stat']['anon']=c.U64
                    if mode=='debt':s['rows'][2]['stat']['active_file']=c.U64
                if mode=='childsum':
                    s['rows'][2]['stat']['anon']=c.U64
                    s['rows'].append(t.node('/cg/a/c',1,owner='/cg/a',anon=1))
                if mode=='positiveSum':
                    s=t.fixture(t.node('/cg/a',c.U64,anon=c.U64,inactive=c.U64))
                with self.subTest(mode=mode):self.assertRaises(ValueError,c.accounting,s)

        def test_other_denials_preserved_with_negative_cell(self):
            s=t.fixture(t.node('/cg/a',200,subtree=True,slab=10,inactive=10),t.node('/cg/a/b',100,owner='/cg/a',anon=1))
            lg=t.legacy(s)
            for mode in ('current','individual','subset','covered','cap','rawnegative','missing','controller','pid','membership','legacy','visibility','missing_snapshot','requestzero','phase','scope'):
                b=copy.deepcopy(s);legacy=copy.deepcopy(lg);q=4*c.GIB;phase='prospective';expected=None
                if mode=='current':b['rows'][1]['current']=99
                if mode=='individual':b['rows'][1]['stat']['active_file']=101
                if mode=='subset':b['rows'][1]['stat']['slab_unreclaimable']=1
                if mode=='covered':b['rows'][1]['cap']=1000
                if mode=='cap':b['rows'][1]['cap']=199
                if mode=='rawnegative':b['rows'][1]['stat']['anon']=-1
                if mode=='missing':del b['rows'][1]['stat']['anon']
                if mode=='controller':b['rows'][2]['owner']='/wrong'
                if mode=='pid':b['rows'][2]['threads']=[99]
                if mode=='membership':b['rows'][2]['populated']=False
                if mode=='legacy':legacy={}
                if mode=='visibility':legacy['visibility_error']='recorded permission error'
                if mode=='missing_snapshot':b=None
                if mode=='requestzero':q=0
                if mode=='phase':phase='unknown'
                if mode=='scope':phase='inside-scope';q=0;expected=dict(high=6*c.GIB,cap=8*c.GIB,swap_max=0,tasks_max=64)
                if mode=='membership':b['rows'][2]['procs']=[999]
                d=go.evaluate(legacy,b,b,q,phase=phase,expected=expected)
                with self.subTest(mode=mode):self.assertFalse(d['allowed']);self.assertIn('error',d)
            self.assertRaises(ValueError,c.pairs,'anon -1')
            self.assertRaises(ValueError,c.pairs,'anon 1\nanon 2')
            with patch.object(c.Path,'read_text',side_effect=PermissionError(13,'denied')):
                self.assertRaises(PermissionError,c.scan)
            with patch.object(c.Path,'read_text',side_effect=FileNotFoundError(2,'missing')),patch.object(c.os,'scandir',return_value=contextlib.nullcontext([])):
                self.assertRaises(FileNotFoundError,c.scan)
            # No usable live boundary in this offline packet.
            self.assertRaises(RuntimeError,go.read_only_admission,phase='prospective',additional_bytes=c.GIB)

        def test_pair_suppresses_both_credits_and_keeps_root(self):
            clean=t.fixture(t.node('/cg/a',200,subtree=True,slab=40,inactive=30,anon=10),t.node('/cg/a/b',100,owner='/cg/a',anon=10))
            bad=copy.deepcopy(clean);bad['rows'][1]['stat']['anon']=0
            for a,b in ((clean,bad),(bad,clean)):
                d=evaluate(a,b);self.assertNotIn('error',d)
                e=d['envelope'][0];self.assertTrue(e['fallback'])
                self.assertEqual((e['inactive_credit'],e['half_slab_credit']),(0,0))
                self.assertEqual(e['reserve'],110)
                self.assertEqual(d['before_accounting']['root_residual_bytes'],c.GIB)
                self.assertEqual(d['after_accounting']['root_residual_bytes'],c.GIB)
                self.assertEqual(d['estimated_total_bytes'],4*c.GIB+c.GIB+110+100+7*c.GIB)

        def test_measured_negative_both_directions(self):
            s=measured['snapshots'];lg=measured['original_legacy']
            for a,b in ((s['before'],s['after']),(s['after'],s['before'])):
                d=go.evaluate(go.legacy_request(lg,4*c.GIB),a,b,4*c.GIB,phase='prospective')
                self.assertNotIn('error',d)
                cell=next(x for x in d['envelope'] if x['path']=='/sys/fs/cgroup/system.slice')
                self.assertTrue(cell['fallback']);self.assertEqual((cell['inactive_credit'],cell['half_slab_credit']),(0,0))
            cell=next(x for x in c.accounting(s['before'])['exclusive'] if x['path']=='/sys/fs/cgroup/system.slice')
            self.assertEqual(cell['exclusive_current'],1085534208)
            self.assertEqual(cell['exclusive_stat']['anon'],-14086144)
            self.assertEqual(cell['negative_debt'],14086144)

        def test_synthetic_actual_GO_and_controls_count_once(self):
            for ancestor in (False,True):
                s=g.scope_fixture(ancestor)
                d=go.evaluate(t.legacy(s,0),s,s,0,phase='inside-scope',expected=g.EXPECTED)
                self.assertTrue(d['allowed'],d)
                self.assertEqual(d['projected_reserved_bytes'],(12 if ancestor else 8)*c.GIB)
                for mode in ('pid','starttime','cap','high','swap','tasks','ancestor','additional'):
                    b=copy.deepcopy(s);lg=t.legacy(s,0);q=0
                    if mode=='pid':b['self_observation']['pid']=43
                    if mode=='starttime':b['self_observation']['starttime']=124
                    if mode=='cap':b['rows'][-1]['cap']=7*c.GIB
                    if mode=='high':b['rows'][-1]['high']=5*c.GIB
                    if mode=='swap':b['rows'][-1]['swap_current']=1
                    if mode=='tasks':b['rows'][-1]['tasks_max']=65
                    if mode=='ancestor':
                        if not ancestor:continue
                        b['rows'][1]['high']=5*c.GIB
                    if mode=='additional':q=1
                    result=go.evaluate(lg,b,b,q,phase='inside-scope',expected=g.EXPECTED)
                    self.assertFalse(result['allowed'],mode)

        def test_strict_frontier_and_available_and_legacy_gates(self):
            for mode in ('frontier','available','legacy_nonreserve'):
                s=t.fixture(t.node('/cg/a',100,cap=51*c.GIB))
                lg=t.legacy(s)
                if mode=='available':s['rows'][1]['cap']=50*c.GIB;lg=t.legacy(s);s['meminfo']['MemAvailable']=6*c.GIB
                if mode=='legacy_nonreserve':s['rows'][1]['cap']=50*c.GIB;lg=t.legacy(s);lg['allowed']=False;lg['reserve_check']=True
                d=evaluate(s,legacy=lg)
                self.assertFalse(d['allowed'],mode)
                self.assertNotIn('error',d)

        def test_formerly_accepted_synthetic_pairs_exact(self):
            count=0
            for current in (0,1,10,100,1000):
                for inactive in range(0,current+1,max(1,current//5)):
                    for slab in (0,(current-inactive)//2,current-inactive):
                        s=t.fixture(t.node('/cg/a',current,inactive=inactive,slab=slab));after=copy.deepcopy(s);after['rows'][1]['current']+=1
                        lg=t.legacy(s)
                        for a,b in ((s,after),(after,s)):
                            before=old['evaluate'](lg,a,b,4*c.GIB,phase='prospective');now=go.evaluate(lg,a,b,4*c.GIB,phase='prospective')
                            self.assertTrue(before['allowed']);count+=1
                            for k in ('allowed','estimated_total_bytes','projected_reserved_bytes','envelope'):
                                self.assertEqual(before[k],now[k])
            self.assertGreater(count,100)
    result=unittest.TextTestRunner(verbosity=2,stream=sys.stderr).run(unittest.defaultTestLoader.loadTestsFromTestCase(ResourceHierarchyTests))
    assert result.wasSuccessful()
    return dict(tests=result.testsRun,synthetic=True,measured_pair_reused=True)
