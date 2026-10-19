import ActualCompPolyGCDTotalRemainderCost

/-! Lift the exact raw Euclidean remainder ledger to the canonical polynomial
GCD called by the retained extractor. Array/normalization and field bit-cost
obligations remain separate. -/
set_option autoImplicit false
namespace AspisR1.CompPolyGCDRemainderBudget
open CompPoly ActualCompPolyGCDCostMirror ActualCompPolyGCDTotalRemainderCost
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

def gcdWithRemainderCost (p q : CPolynomial F) : CPolynomial F × Nat :=
  let r := gcdMonicWithCostPublic p.val q.val
  (CPolynomial.ofArray r.1,r.2)

theorem gcdWithRemainderCost_value (p q : CPolynomial F) :
    (gcdWithRemainderCost p q).1 = CPolynomial.gcdMonic p q := by
  change CPolynomial.ofArray (gcdMonicWithCostPublic p.val q.val).1 =
    CPolynomial.ofArray (CPolynomial.Raw.gcdMonic p.val q.val)
  exact congrArg (fun r : CPolynomial.Raw F => CPolynomial.ofArray r)
    (gcdMonicWithCostPublic_value p.val q.val)

theorem gcdWithRemainderCost_le (p q : CPolynomial F) (N : Nat)
    (hp : p.size ≤ N) (hq : q.size ≤ N) :
    (gcdWithRemainderCost p q).2 ≤
      (2*N+1)*(100*N^3+800*N^2+1606*N+5) :=
  public_gcd_remainder_cost_uniform p.val q.val N hp hq

/-- A bit-operation charge bounded by beta per charged field operation lifts
this ledger uniformly. This does not supply beta for the field backend. -/
theorem gcdWithRemainderBitCharge_le (p q : CPolynomial F) (N beta : Nat)
    (hp : p.size ≤ N) (hq : q.size ≤ N) :
    beta*(gcdWithRemainderCost p q).2 ≤
      beta*((2*N+1)*(100*N^3+800*N^2+1606*N+5)) :=
  Nat.mul_le_mul_left beta (gcdWithRemainderCost_le p q N hp hq)

#print axioms gcdWithRemainderCost_value
#print axioms gcdWithRemainderCost_le
#print axioms gcdWithRemainderBitCharge_le
end AspisR1.CompPolyGCDRemainderBudget
