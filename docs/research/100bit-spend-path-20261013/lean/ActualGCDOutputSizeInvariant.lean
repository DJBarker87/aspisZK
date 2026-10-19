import ActualRawModRemainderDegreeBridge
import ActualGCDOuterRemainderCount
import ActualModularProductDegreeBound

namespace ActualGCDOutputSizeInvariant
open CompPoly
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

private theorem monicNormalize_size_le (p : CPolynomial.Raw F) :
    p.monicNormalize.size ≤ p.size := by
  by_cases hp0 : p.trim = (0 : CPolynomial.Raw F)
  · simp [CPolynomial.Raw.monicNormalize, hp0]
  · rw [ActualModularProductDegreeBound.monicNormalize_size_eq_trim p hp0]
    exact CPolynomial.Raw.Trim.size_le_size p

theorem counted_gcd_output_size_le (fuel : Nat) (p q : CPolynomial.Raw F) :
    (ActualGCDOuterRemainderCount.gcdWithRemainderCount fuel p q).1.size ≤
      max p.size q.size := by
  induction fuel generalizing p q with
  | zero =>
      simp only [ActualGCDOuterRemainderCount.gcdWithRemainderCount]
      change p.monicNormalize.size ≤ max p.size q.size
      exact (monicNormalize_size_le p).trans (le_max_left p.size q.size)
  | succ fuel ih =>
      simp only [ActualGCDOuterRemainderCount.gcdWithRemainderCount]
      change (if (q.trim == (0 : CPolynomial.Raw F)) = true then
        (p.trim.monicNormalize, 0) else
        ((ActualGCDOuterRemainderCount.gcdWithRemainderCount fuel
          q.trim (p.trim % q.trim)).1,
         (ActualGCDOuterRemainderCount.gcdWithRemainderCount fuel
          q.trim (p.trim % q.trim)).2 + 1)).1.size ≤ max p.size q.size
      by_cases hzero : q.trim = (0 : CPolynomial.Raw F)
      · have hbool : (q.trim == (0 : CPolynomial.Raw F)) = true := by simp [hzero]
        rw [if_pos hbool]
        change p.trim.monicNormalize.size ≤ max p.size q.size
        exact (monicNormalize_size_le p.trim).trans
          ((le_max_left p.trim.size q.trim.size).trans
            (max_le_max (CPolynomial.Raw.Trim.size_le_size p)
              (CPolynomial.Raw.Trim.size_le_size q)))
      · have hbool : ¬ (q.trim == (0 : CPolynomial.Raw F)) = true := by
          intro h
          apply hzero
          exact LawfulBEq.eq_of_beq (by simpa using h)
        rw [if_neg hbool]
        have hqt0 : q.trim ≠ (0 : CPolynomial.Raw F) := hzero
        have hrem := ActualRawModRemainderDegreeBridge.rawMod_size_le_divisor
          p.trim q.trim (CPolynomial.Raw.Trim.trim_twice p)
          (CPolynomial.Raw.Trim.trim_twice q) hqt0
        have hrec := ih q.trim (p.trim % q.trim)
        have hbound := hrec.trans ((le_of_eq (max_eq_left hrem)).trans
          ((CPolynomial.Raw.Trim.size_le_size q).trans (le_max_right p.size q.size)))
        exact hbound

theorem actual_gcd_output_size_le (p q : CPolynomial.Raw F) :
    (CPolynomial.Raw.gcdMonic p q).size ≤ max p.size q.size := by
  rw [← ActualGCDOuterRemainderCount.gcdMonicCounted_value]
  exact counted_gcd_output_size_le (p.size + q.size + 1) p q

#print axioms counted_gcd_output_size_le
#print axioms actual_gcd_output_size_le
end ActualGCDOutputSizeInvariant
