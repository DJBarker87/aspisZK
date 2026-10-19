import ActualCompPolyGCDCostMirror
import ActualRawModCostBound
import ActualRawModRemainderDegreeBridge

/-! Uniform polynomial bound on the complete retained Euclidean remainder
ledger. This bounds the exact value-preserving mirror, including failure/fuel
prefixes, not yet the extractor's bit cost or normalization/array overhead. -/
set_option autoImplicit false
namespace ActualCompPolyGCDTotalRemainderCost
open CompPoly ActualCompPolyGCDCostMirror ActualRawModRemainderCostBridge
open ActualRawModCostBound
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

theorem gcd_remainder_cost_le (fuel N : Nat) (p q : CPolynomial.Raw F)
    (hpN : p.size ≤ N) (hqN : q.size ≤ N) :
    (gcdMonicWithCost fuel p q).2 ≤ fuel * modBudget N := by
  induction fuel generalizing p q with
  | zero => simp [gcdMonicWithCost]
  | succ fuel ih =>
    simp only [gcdMonicWithCost]
    by_cases hz : (q.trim == (0 : CPolynomial.Raw F)) = true
    · have heq : q.trim = (#[] : CPolynomial.Raw F) := LawfulBEq.eq_of_beq hz
      simp [heq]
    · simp only [hz,↓reduceIte]
      have hpT : p.trim.size ≤ N :=
        (CPolynomial.Raw.Trim.size_le_size p).trans hpN
      have hqT : q.trim.size ≤ N :=
        (CPolynomial.Raw.Trim.size_le_size q).trans hqN
      have hq0 : q.trim ≠ (0 : CPolynomial.Raw F) := by
        intro he
        exact hz (by simp [he])
      have hrem : (rawModWithCost p.trim q.trim).1.size ≤ N := by
        rw [rawModWithCost_value]
        exact (ActualRawModRemainderDegreeBridge.rawMod_size_le_divisor
          p.trim q.trim (CPolynomial.Raw.Trim.trim_twice p)
          (CPolynomial.Raw.Trim.trim_twice q) hq0).trans hqT
      have htail := ih q.trim (rawModWithCost p.trim q.trim).1 hqT hrem
      have hstep := raw_mod_cost_le p.trim q.trim N
        (CPolynomial.Raw.Trim.trim_twice q) hq0 hpT hqT
      calc
        _ ≤ fuel * modBudget N + modBudget N := Nat.add_le_add htail hstep
        _ = (fuel+1)*modBudget N := by rw [Nat.add_mul,Nat.one_mul]

theorem public_gcd_remainder_cost_le (p q : CPolynomial.Raw F) :
    (gcdMonicWithCostPublic p q).2 ≤
      (p.size+q.size+1) * modBudget (max p.size q.size) := by
  exact gcd_remainder_cost_le (p.size+q.size+1) (max p.size q.size)
    p q (Nat.le_max_left ..) (Nat.le_max_right ..)


theorem modBudget_polynomial (N : Nat) :
    modBudget N = 100*N^3 + 800*N^2 + 1606*N + 5 := by
  unfold modBudget
  ring

theorem public_gcd_remainder_cost_uniform (p q : CPolynomial.Raw F) (N : Nat)
    (hpN : p.size ≤ N) (hqN : q.size ≤ N) :
    (gcdMonicWithCostPublic p q).2 ≤
      (2*N+1)*(100*N^3 + 800*N^2 + 1606*N + 5) := by
  have h := gcd_remainder_cost_le (p.size+q.size+1) N p q hpN hqN
  have hfuel : p.size+q.size+1 ≤ 2*N+1 := by omega
  have hm := Nat.mul_le_mul_right (modBudget N) hfuel
  rw [modBudget_polynomial] at h hm
  exact h.trans hm

#print axioms modBudget_polynomial
#print axioms public_gcd_remainder_cost_uniform

#print axioms gcd_remainder_cost_le
#print axioms public_gcd_remainder_cost_le
end ActualCompPolyGCDTotalRemainderCost
