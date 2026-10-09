import random, unittest
from aspis_completion.polynomial import *
from aspis_completion.masking import *
from aspis_completion.extraction import *
from aspis_completion.cost import *

class DecoderTests(unittest.TestCase):
    def test_polynomial_division(self):
        p=101;a=[1,2,3];b=[4,5]
        q,r=divmod_poly(multiply(a,b,p),b,p)
        self.assertEqual(q,a);self.assertEqual(r,[])
    def test_random_bw(self):
        rng=random.Random(1729)
        for p in (19,31,101):
            for k in (1,2,4):
                for t in (0,1,2):
                    for repeat in range(8):
                        n=k+2*t+2;xs=list(range(n));poly=[rng.randrange(p) for _ in range(k)]
                        ys=[evaluate(poly,x,p) for x in xs]
                        bad=rng.sample(range(n),t)
                        for i in bad:ys[i]=(ys[i]+rng.randrange(1,p))%p
                        self.assertEqual(berlekamp_welch(xs,ys,k,t,p),tuple(poly))
    def test_insufficient_and_duplicate(self):
        with self.assertRaises(DecodeError):berlekamp_welch([0,1],[1,2],2,1,19)
        with self.assertRaises(DecodeError):berlekamp_welch([0,0,1],[1,1,2],1,1,19)
    def test_inconsistent_linear(self):
        with self.assertRaises(DecodeError):solve_linear([[1],[1]],[1,2],19)
    def test_composite_field(self):
        with self.assertRaises(ValueError):require_prime(21)
    def test_common_support(self):
        xs=list(range(12)); polys=tuple((i+1,i+2,i+3) for i in range(4))
        cols=[[evaluate(poly,x,101) for x in xs] for poly in polys]
        for col in cols:col[2]=(col[2]+1)%101;col[5]=(col[5]+2)%101
        self.assertEqual(decode_columns(xs,cols,3,2,101),polys)
    def test_disjoint_support_exceeds_joint_budget(self):
        xs=list(range(8));polys=((1,2),(3,4));cols=[[evaluate(p,x,31) for x in xs] for p in polys]
        cols[0][1]=(cols[0][1]+1)%31;cols[1][2]=(cols[1][2]+1)%31
        with self.assertRaises(DecodeError):decode_columns(xs,cols,2,1,31)
    def test_mask_shift_in_span(self):
        matrix=[[1,0],[0,1],[1,1]];shift=[2,3,5]
        self.assertTrue(witness_shift_hidden(matrix,shift,7))
        self.assertEqual(view_histogram(matrix,[0,0,0],7),view_histogram(matrix,shift,7))
    def test_mask_leak(self):
        matrix=[[1],[0]];shift=[0,1]
        self.assertFalse(witness_shift_hidden(matrix,shift,7))
        self.assertNotEqual(view_histogram(matrix,[0,0],7),view_histogram(matrix,shift,7))
    def test_checked_search(self):
        r=first_valid([1,2,3],lambda x:x==2,3)
        self.assertEqual((r.status,r.witness,r.checked),('VALIDATED',2,2))
        r=first_valid([1,2,3],lambda x:x==3,2)
        self.assertEqual(r.status,'BUDGET_EXHAUSTED');self.assertIsNone(r.witness)
    def test_amount_controls(self):
        self.assertTrue(amounts_valid(TransferAmounts(1000,600,400)))
        for a in (TransferAmounts(1000,0,1000),TransferAmounts(1000,1000,0),
                  TransferAmounts(1000,600,401),TransferAmounts((1<<30),1,(1<<30)-1)):
            self.assertFalse(amounts_valid(a))
    def test_unknown_cu(self):
        result=envelope(1105880,[Component('PDA',None,None,None,None)],1400000)
        self.assertEqual(result['status'],'BLOCKED')

    def test_sixteen_columns_one_support(self):
        rng=random.Random(2026);p=65537;k=16;t=8;xs=list(range(48))
        polys=tuple(tuple(rng.randrange(p) for _ in range(k)) for _ in range(16))
        cols=[[evaluate(poly,x,p) for x in xs] for poly in polys]
        support=rng.sample(range(len(xs)),t)
        for col in cols:
            for i in support:col[i]=(col[i]+1)%p
        self.assertEqual(decode_columns(xs,cols,k,t,p),polys)
