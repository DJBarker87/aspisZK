import unittest
from fractions import Fraction
from aspis_completion.query_sampling import *
class QueryTests(unittest.TestCase):
    def test_all_small(self):
        for n in range(1,20):
            for m in range(n+1):
                for q in range(n+1):
                    self.assertLessEqual(all_in_subset(n,m,q),with_replacement_ceiling(n,m,q))
    def test_pinned_diagnostic(self):
        p=all_in_subset(262144,262144-15335,22)
        self.assertGreater(p,Fraction(1,4))
        self.assertLess(p,Fraction(3,10))
    def test_impossible(self):
        self.assertEqual(all_in_subset(100,3,4),0)
