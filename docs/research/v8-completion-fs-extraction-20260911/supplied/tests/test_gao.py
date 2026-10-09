import random,unittest
from aspis_completion.gao import *
from aspis_completion.polynomial import berlekamp_welch,evaluate
class GaoTests(unittest.TestCase):
    def test_two_independent_decoder_algorithms(self):
        rng=random.Random(7811)
        for p in (19,31,101):
            for k in (1,2,4):
                for t in (0,1,2):
                    for _ in range(8):
                        xs=list(range(k+2*t+2));poly=[rng.randrange(p) for _ in range(k)]
                        ys=[evaluate(poly,x,p) for x in xs]
                        for i in rng.sample(range(len(xs)),t):ys[i]=(ys[i]+rng.randrange(1,p))%p
                        self.assertEqual(gao_decode(xs,ys,k,t,p),tuple(poly))
                        self.assertEqual(gao_decode(xs,ys,k,t,p),berlekamp_welch(xs,ys,k,t,p))
    def test_larger(self):
        rng=random.Random(7831);p=65537;k=64;t=12;xs=list(range(128));poly=[rng.randrange(p) for _ in range(k)]
        ys=[evaluate(poly,x,p) for x in xs]
        for i in rng.sample(range(128),t):ys[i]=(ys[i]+1)%p
        self.assertEqual(gao_decode(xs,ys,k,t,p),tuple(poly))
    def test_zero_polynomial(self):
        self.assertEqual(gao_decode(list(range(9)),[0]*9,3,2,31),(0,0,0))
    def test_interpolation(self):
        self.assertEqual(interpolate([0,1,2],[1,6,17],31),[1,2,3])

    def test_m31_larger_reference_instance(self):
        rng=random.Random(991);p=2147483647;k=256;t=128;xs=list(range(520))
        poly=[rng.randrange(p) for _ in range(k)];ys=[evaluate(poly,x,p) for x in xs]
        for i in rng.sample(range(len(xs)),t):ys[i]=(ys[i]+rng.randrange(1,p))%p
        self.assertEqual(gao_decode(xs,ys,k,t,p),tuple(poly))
    def test_exact_capacity_and_fewer_errors(self):
        rng=random.Random(818);p=101;k=4;t=3;xs=list(range(k+2*t))
        for errors in range(t+1):
            poly=[rng.randrange(p) for _ in range(k)];ys=[evaluate(poly,x,p) for x in xs]
            for i in rng.sample(range(len(xs)),errors):ys[i]=(ys[i]+1)%p
            self.assertEqual(gao_decode(xs,ys,k,t,p),tuple(poly))
            self.assertEqual(berlekamp_welch(xs,ys,k,t,p),tuple(poly))
