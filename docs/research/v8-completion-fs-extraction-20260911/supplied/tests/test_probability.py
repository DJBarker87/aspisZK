import unittest
from fractions import Fraction as F
from aspis_completion.finite_rom import *
from aspis_completion.sampling import *
from aspis_completion.security import *

class ProbabilityTests(unittest.TestCase):
    def test_adaptive_grinding_exact(self):
        for alphabet in (2,3,5):
            for fuel in range(1,6):
                policy=lambda h: None if any(s.answer==0 for s in h) else len(h)
                result=enumerate_rom(alphabet,fuel,policy,lambda h,m:frozenset({0}))
                self.assertEqual(result.bad_mass,grinding_success(alphabet,fuel))
                self.assertLessEqual(result.bad_mass,F(fuel,alphabet))
    def test_cached_query_not_independent(self):
        result=enumerate_rom(5,5,lambda h:'same',lambda h,m:frozenset({0}))
        self.assertEqual(result.bad_mass,F(1,5));self.assertEqual(result.expected_fresh,1)
    def test_adaptive_bad_sets(self):
        result=enumerate_rom(5,4,lambda h:len(h),
             lambda h,m:frozenset({sum(s.answer for s in h)%5}))
        self.assertEqual(result.bad_mass,1-F(4,5)**4)
    def test_late_target_control(self):
        # Choosing B={answer} AFTER seeing it gives probability 1, not 1/5.
        result=enumerate_rom(5,1,lambda h:'x',lambda h,m:frozenset())
        late=sum(m for h,m in result.distribution.items() if h[0].answer in {h[0].answer})
        self.assertEqual(late,1)
    def test_abort_distribution(self):
        dist=retry_distribution(range(4),lambda x:None if x==3 else x,3)
        self.assertEqual(dist[None],F(1,64));assert_uniform_success(dist)
        self.assertEqual(sum(dist.values()),1)
    def test_zero_attempts(self):
        self.assertEqual(retry_distribution(range(4),lambda x:x,0),{None:F(1)})
    def test_distinct_pair_unconditional(self):
        for n in range(2,8):
            raw=range(n+2);dec=lambda x,n=n:x if x<n else None
            dist=ordered_pair_distribution(raw,dec,3,3)
            self.assertEqual(sum(dist.values()),1)
            for m in range(n+1):
                got=sum(p for pair,p in dist.items() if pair is not None and pair[0]<m and pair[1]<m)
                self.assertLessEqual(got,target_pair_bound(n,m))
    def test_biased_decoder_rejected(self):
        dist=retry_distribution(range(4),lambda x:x%3,3)
        with self.assertRaises(ValueError):assert_uniform_success(dist)
    def test_pair_constants(self):
        self.assertGreater(bits(PAIR_BOUND),195)
        self.assertLess(bits(PAIR_BOUND),196)
    def test_retry_diagnostic_not_global(self):
        self.assertGreater(bits(REPORTED_RESIDUAL_CEILING),103)
        self.assertLess(bits(REPORTED_RESIDUAL_CEILING),104)
        self.assertLess(bits(retry_union(REPORTED_RESIDUAL_CEILING,16)),100)
    def test_unknown_ledger_blocks(self):
        r=certificate([Term('residual',REPORTED_RESIDUAL_CEILING,None,None,'conditional')])
        self.assertEqual(r['status'],'BLOCKED')
    def test_resource_bounds(self):
        self.assertEqual(collision_bound(1),0)
        self.assertEqual(collision_bound(2,8),F(1,256))
        self.assertEqual(target_bound(2,3,8),F(6,256))
        self.assertLess(bits(collision_bound(1<<64)),100)
    def test_source_names_do_not_make_numeric_fail_pass(self):
        r=certificate([Term('bad',F(1,2),'t','s','global')],
             partition_theorem='p',extracted_witness_theorem='e')
        self.assertEqual(r['status'],'NUMERIC_FAIL')
