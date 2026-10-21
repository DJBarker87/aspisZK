import OraclePortCoverageDraft
import BinMultiproof

/-! The sparse tree route is the exact public binary index, not merely some
18-edge path. Generic height induction avoids enumerating a leaf universe. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRouteIndexC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree OracleDecisionMultiBuild OracleDecisionMultiRecovery
open BinMultiproof (slots slot)

theorem slots_period (h i : Nat) : slots h (i+2^h) = slots h i := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih =>
    have parity : slot (i+2^(h+1)) = slot i := by
      apply Fin.ext
      change (i+2^(h+1))%2 = i%2
      rw [Nat.pow_succ]
      omega
    have division : (i+2^(h+1))/2 = i/2+2^h := by
      rw [Nat.pow_succ]
      omega
    simp only [slots,parity,division,ih]

theorem slots_snoc (h i : Nat) :
    slots (h+1) i = slots h i ++ [slot (i/2^h)] := by
  induction h generalizing i with
  | zero => simp only [slots,Nat.pow_zero,Nat.div_one,List.nil_append]
  | succ h ih =>
    rw [slots,slots,ih]
    rw [Nat.div_div_eq_div_mul]
    congr 2
    rw [Nat.pow_succ,Nat.mul_comm]

theorem opened_exact (is : List Nat) (f : Nat → Bytes) (s : Nat → Nat → State)
    (h base i : Nat) (member : i ∈ is) (lo : base ≤ i) (hi : i < base+2^h) :
    OpenedAt (build is f s h base) (slots h (i-base)).reverse (f i) := by
  induction h generalizing base with
  | zero =>
    have same : i = base := by omega
    subst i
    rw [build,if_pos ((occupied_zero is base).mpr member)]
    exact .leaf _
  | succ h ih =>
    have occupied : Occupied is (h+1) base := ⟨i,member,lo,hi⟩
    rw [build,if_pos occupied,slots_snoc,List.reverse_append]
    by_cases left : i < base+2^h
    · have digit : (i-base)/2^h = 0 := Nat.div_eq_of_lt (by omega)
      rw [digit]
      change OpenedAt _ (0 :: (slots h (i-base)).reverse) _
      exact .left (ih base lo left)
    · have low : base+2^h ≤ i := by omega
      have high : i < base+2^h+2^h := by rw [Nat.pow_succ] at hi; omega
      have digit : (i-base)/2^h = 1 := by
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have difference : i-base = (i-(base+2^h))+2^h := by omega
      rw [digit,difference,slots_period]
      change OpenedAt _ (1 :: (slots h (i-(base+2^h))).reverse) _
      exact .right (ih (base+2^h) low high)

#print axioms slots_period
#print axioms slots_snoc
#print axioms opened_exact
end AspisR1.OraclePortRouteIndexC4
end
