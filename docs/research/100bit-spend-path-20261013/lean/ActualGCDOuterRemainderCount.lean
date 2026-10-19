import CompPoly.Univariate.EuclideanAlgorithm

namespace ActualGCDOuterRemainderCount
open CompPoly

variable {F : Type*} [BEq F] [Field F]

def gcdWithRemainderCount : Nat → CPolynomial.Raw F → CPolynomial.Raw F →
    CPolynomial.Raw F × Nat
  | 0, p, _ => (p.monicNormalize, 0)
  | n + 1, p, q =>
      let p := p.trim
      let q := q.trim
      if (q == 0) = true then (p.monicNormalize, 0)
      else
        let tail := gcdWithRemainderCount n q (p % q)
        (tail.1, tail.2 + 1)
termination_by fuel _ _ => fuel

theorem gcdWithRemainderCount_value (fuel : Nat) (p q : CPolynomial.Raw F) :
    (gcdWithRemainderCount fuel p q).1 =
      CPolynomial.Raw.gcdMonicWithFuel fuel p q := by
  induction fuel generalizing p q with
  | zero => simp [gcdWithRemainderCount, CPolynomial.Raw.gcdMonicWithFuel]
  | succ fuel ih =>
      simp [gcdWithRemainderCount, CPolynomial.Raw.gcdMonicWithFuel,
        CPolynomial.Raw.gcdMonicWithFuel._f]
      split <;> simp_all

theorem gcdWithRemainderCount_count_le (fuel : Nat) (p q : CPolynomial.Raw F) :
    (gcdWithRemainderCount fuel p q).2 ≤ fuel := by
  induction fuel generalizing p q with
  | zero => simp [gcdWithRemainderCount]
  | succ fuel ih =>
      simp only [gcdWithRemainderCount]
      split
      · simp
      · have htail := ih q.trim (p.trim % q.trim)
        omega

def gcdMonicCounted {F : Type*} [BEq F] [Field F]
    (p q : CPolynomial.Raw F) : CPolynomial.Raw F × Nat :=
  gcdWithRemainderCount (p.size + q.size + 1) p q

theorem gcdMonicCounted_value {F : Type*} [BEq F] [Field F]
    (p q : CPolynomial.Raw F) :
    (gcdMonicCounted p q).1 = CPolynomial.Raw.gcdMonic p q := by
  simp [gcdMonicCounted, CPolynomial.Raw.gcdMonic,
    gcdWithRemainderCount_value]

theorem gcdMonicCounted_remainder_count_le {F : Type*} [BEq F] [Field F]
    (p q : CPolynomial.Raw F) :
    (gcdMonicCounted p q).2 ≤ p.size + q.size + 1 := by
  exact gcdWithRemainderCount_count_le _ _ _

#print axioms gcdWithRemainderCount_value
#print axioms gcdWithRemainderCount_count_le
#print axioms gcdMonicCounted_value
#print axioms gcdMonicCounted_remainder_count_le
end ActualGCDOuterRemainderCount
