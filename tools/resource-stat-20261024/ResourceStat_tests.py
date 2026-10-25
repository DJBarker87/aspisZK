"""Offline only; unchanged historical suite plus explicit candidate contract delta."""
import copy
import importlib.util
from pathlib import Path
import sys
import unittest

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'baseline'))

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);sys.modules[name]=obj
    spec.loader.exec_module(obj)
    return obj


def suite(candidate=False):
    module('resource_slab_candidate',HERE/('ResourceStat_candidate.py' if candidate else 'baseline/resource_slab_candidate.py'))
    module('go_api',HERE/('ResourceStat_go.py' if candidate else 'baseline/go_api.py'))
    t=module('test_resource_slab',HERE/'baseline/test_resource_slab.py')
    g=module('test_go_api',HERE/'baseline/test_go_api.py')
    if candidate:
        # Explicit expected-denial change: the second historical input (60+60)
        # now fully charges 120. The individual-over-current case still denies.
        def revised(self):
            s=t.fixture(t.node('/cg/a',100,slab=101))
            self.assertRaises(ValueError,t.accounting,s)
            s=t.fixture(t.node('/cg/a',100,slab=60,inactive=60))
            a=t.accounting(s)
            self.assertEqual(a['uncovered_reserve_bytes'],120)
            self.assertEqual(a['half_slab_credit_bytes'],0)
            self.assertEqual(a['inactive_file_credit_bytes'],0)
        t.CandidateTests.test_components_exceed_current=revised
        # This test exercises the byte-identical historical transport, not a
        # ResourceStat collector (none is installed or run). Keep its old schema
        # expectation scoped to that test; all candidate decisions use new API.
        transport_test=g.GoCollectorTests.test_remote_payload_and_receipt_without_host
        def historical_transport(self):
            from unittest.mock import patch
            with patch.object(g.go,'API_VERSION','ResourceGO-phase-v1'):
                transport_test(self)
        g.GoCollectorTests.test_remote_payload_and_receipt_without_host=historical_transport
    result=unittest.TestSuite([unittest.defaultTestLoader.loadTestsFromModule(t),unittest.defaultTestLoader.loadTestsFromModule(g)])
    return result,t,sys.modules['resource_slab_candidate'],sys.modules['go_api']


def extra(t,c,go):
    class ResourceStatTests(unittest.TestCase):
        def test_large_deficit_and_both_snapshot_directions(self):
            consistent=t.fixture(t.node('/cg/a',1000,slab=100,inactive=800,kernel=100))
            bad=copy.deepcopy(consistent)
            bad['rows'][1]['stat'].update(active_file=900,anon=1000,kernel=1000)
            for a,b in ((consistent,bad),(bad,consistent)):
                for fn in (lambda: c.propose(t.legacy(consistent),a,b,4*c.GIB),
                           lambda: go.evaluate(t.legacy(consistent),a,b,4*c.GIB,phase='prospective')):
                    d=fn();self.assertNotIn('error',d)
                    e=d['envelope'][0]
                    self.assertTrue(e['fallback']);self.assertEqual(e['usage'],3700)
                    self.assertEqual(e['reserve'],3700)
                    self.assertEqual(e['inactive_credit'],0);self.assertEqual(e['half_slab_credit'],0)
                    self.assertEqual(d['before_accounting']['root_residual_bytes'],c.GIB)
                    self.assertEqual(d['after_accounting']['root_residual_bytes'],c.GIB)

        def test_valid_inputs_exact_numeric_preservation(self):
            old=module('ResourceStat_old_reference',HERE/'baseline/resource_slab_candidate.py')
            import runpy
            oldgo=runpy.run_path(str(HERE/'baseline/go_api.py'))
            for current in (0,1,10,100,1000):
                for inactive in range(0,current+1,max(1,current//5)):
                    for slab in (0,(current-inactive)//2,current-inactive):
                        s=t.fixture(t.node('/cg/a',current,slab=slab,inactive=inactive))
                        after=copy.deepcopy(s);after['rows'][1]['current']+=1
                        legacy=t.legacy(s)
                        for before,now in ((old.propose(legacy,s,after,4*c.GIB),c.propose(legacy,s,after,4*c.GIB)),
                            (oldgo['evaluate'](legacy,s,after,4*c.GIB,phase='prospective'),go.evaluate(legacy,s,after,4*c.GIB,phase='prospective'))):
                            for key in ('estimated_total_bytes','allowed','projected_reserved_bytes'):
                                self.assertEqual(before[key],now[key])
                            self.assertEqual(before['envelope'][0]['reserve'],now['envelope'][0]['reserve'])

        def test_nested_fallback_and_extra_residual_reserve(self):
            s=t.fixture(t.node('/cg/a',200,subtree=True,inactive=60,anon=160),
                        t.node('/cg/a/b',100,owner='/cg/a',anon=100))
            a=c.accounting(s)
            self.assertEqual(a['exclusive'][0]['disjoint_total'],120)
            self.assertEqual(a['uncovered_reserve_bytes'],220)
            self.assertEqual(a['root_residual_bytes'],c.GIB)
            s['rows'][1]['cap']=1000
            self.assertRaises(ValueError,c.accounting,s) # covered inconsistency

        def test_fallback_does_not_bypass_other_errors(self):
            s=t.fixture(t.node('/cg/a',100,slab=40,inactive=60,anon=60,kernel=40))
            for change in ('missing','negative','overflow','subset','individual','overcap','visibility','membership'):
                b=copy.deepcopy(s);old=t.legacy(s)
                if change=='missing':del b['rows'][1]['stat']['anon']
                if change=='negative':b['rows'][1]['stat']['anon']=-1
                if change=='overflow':b['rows'][1]['stat']['anon']=c.U64+1
                if change=='subset':b['rows'][1]['stat']['slab_unreclaimable']=1
                if change=='individual':b['rows'][1]['stat']['active_file']=101
                if change=='overcap':b['rows'][1]['cap']=99
                if change=='visibility':old['visibility_error']='permission denied'
                if change=='membership':b['rows'][1]['threads']=[99]
                self.assertFalse(c.propose(old,b,b,4*c.GIB)['allowed'],change)
                self.assertFalse(go.evaluate(old,b,b,4*c.GIB,phase='prospective')['allowed'],change)

        def test_empty_charged_fallback(self):
            s=t.fixture(t.node('/cg/a',100,populated=False,cap=1000,inactive=60,anon=60))
            a=c.accounting(s)
            self.assertEqual(a['bounded_reserved_bytes'],0)
            self.assertEqual(a['uncovered_reserve_bytes'],120)

        def test_sum_overflow_denies(self):
            s=t.fixture(t.node('/cg/a',c.U64,inactive=c.U64,anon=c.U64))
            self.assertRaises(ValueError,c.accounting,s)

        def test_lazyfree_overlap_shape_fully_charged(self):
            s=t.fixture(t.node('/cg/a',100,inactive=100,anon=100))
            a=c.accounting(s)
            self.assertEqual(a['uncovered_reserve_bytes'],200)
            self.assertEqual(a['inactive_file_credit_bytes'],0)
    return unittest.defaultTestLoader.loadTestsFromTestCase(ResourceStatTests)


def main():
    runner=unittest.TextTestRunner(verbosity=2)
    baseline,_,_,_=suite(False)
    first=runner.run(baseline)
    candidate,t,c,g=suite(True)
    candidate.addTests(extra(t,c,g))
    second=runner.run(candidate)
    assert first.testsRun==57,(first.testsRun,'historical test count')
    return 0 if first.wasSuccessful() and second.wasSuccessful() else 1

if __name__=='__main__':raise SystemExit(main())
