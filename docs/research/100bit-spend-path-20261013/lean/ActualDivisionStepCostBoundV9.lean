import ActualRawLongDivisionCostV4
import ActualRawPowCoefficientBudget
import RawMulSizeBoundV5
import Mathlib.Tactic.Ring

namespace ActualDivisionStepCostBound
open CompPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

private theorem rawMulCoefficientBudget_le_sizes (p q : CPolynomial.Raw F)
    (A B : Nat) (hp : p.size ≤ A) (hq : q.size ≤ B) :
    ActualRawPowCoefficientBudget.rawMulCoefficientBudget p q ≤
      A * B + A * (A + B) + (A + B) := by
  unfold ActualRawPowCoefficientBudget.rawMulCoefficientBudget
  have h1 : p.size * q.size ≤ A * B := Nat.mul_le_mul hp hq
  have h2 : p.size * (p.size + q.size) ≤ A * (A + B) :=
    (Nat.mul_le_mul_left p.size (Nat.add_le_add hp hq)).trans
      (Nat.mul_le_mul_right (A + B) hp)
  have h3 : p.size + q.size ≤ A + B := Nat.add_le_add hp hq
  omega

/-- Cost of the exact active branch of the pinned long-division mirror when
all current arrays have degree/length at most N. -/
theorem active_step_budget_le (p q quotientTail : CPolynomial.Raw F)
    (N : Nat) (hN : 1 ≤ N)
    (hp : p.size ≤ N) (hq : q.size ≤ N)
    (ht : quotientTail.size ≤ N + 1) :
    ActualRawLongDivisionCostV2.activeDivisionStepBudget p q quotientTail ≤
      100 * (N + 3) * (N + 3) := by
  let k := p.size - q.size
  let xShift := (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k
  let shiftedQ := q * xShift
  let scaledQ := CPolynomial.Raw.C p.leadingCoeff * shiftedQ
  let quotientTerm := CPolynomial.Raw.C p.leadingCoeff * xShift
  have hk : k ≤ N := by dsimp [k]; omega
  have hxsize : xShift.size = k + 1 := by
    dsimp [xShift, k]
    exact ActualRawPowCoefficientBudget.rawXpow_size _
  have hshift : shiftedQ.size ≤ 2 * N + 2 := by
    dsimp [shiftedQ]
    have hm := RawMulSizeBound.raw_mul_size_le q xShift
    omega
  have hCsize : (CPolynomial.Raw.C p.leadingCoeff : CPolynomial.Raw F).size = 1 := rfl
  have hscaled : scaledQ.size ≤ 2 * N + 4 := by
    dsimp [scaledQ]
    have hm := RawMulSizeBound.raw_mul_size_le
      (CPolynomial.Raw.C p.leadingCoeff) shiftedQ
    omega
  have hterm : quotientTerm.size ≤ N + 3 := by
    dsimp [quotientTerm]
    have hm := RawMulSizeBound.raw_mul_size_le
      (CPolynomial.Raw.C p.leadingCoeff) xShift
    omega
  have hpow : (ActualRawPowCoefficientBudget.rawPowWithCoefficientBudget
      (CPolynomial.Raw.X : CPolynomial.Raw F) k).2 ≤ 12 * N * (N + 1) := by
    calc
      _ ≤ 12 * k * (k + 1) :=
        ActualRawPowCoefficientBudget.rawXpow_coefficient_budget_le k
      _ ≤ 12 * N * (N + 1) := by
        have hmul := Nat.mul_le_mul hk (Nat.succ_le_succ hk)
        calc
          12 * k * (k + 1) = 12 * (k * (k + 1)) := by ring
          _ ≤ 12 * (N * (N + 1)) := Nat.mul_le_mul_left 12 hmul
          _ = 12 * N * (N + 1) := by ring
  have hmulShift := rawMulCoefficientBudget_le_sizes q xShift N (N + 1) hq
    (by omega)
  have hmulScale := rawMulCoefficientBudget_le_sizes
    (CPolynomial.Raw.C p.leadingCoeff) shiftedQ 1 (2 * N + 2) (Nat.le_of_eq hCsize) hshift
  have hmulTerm := rawMulCoefficientBudget_le_sizes
    (CPolynomial.Raw.C p.leadingCoeff) xShift 1 (N + 1) (Nat.le_of_eq hCsize) (by omega)
  have hmaxScaled : max p.size scaledQ.size ≤ 2 * N + 4 := by omega
  have hmaxTerm : max quotientTail.size quotientTerm.size ≤ N + 3 := by omega
  have hpowActual : (ActualRawPowCoefficientBudget.rawPowWithCoefficientBudget
      (CPolynomial.Raw.X : CPolynomial.Raw F) (p.size - q.size)).2 ≤ 12 * N * (N + 1) := by
    simpa [k] using hpow
  have hshiftBound : ActualRawPowCoefficientBudget.rawMulCoefficientBudget q xShift ≤
      N * (N + 1) + N * (N + (N + 1)) + (N + (N + 1)) := by
    simpa only [ActualRawPowCoefficientBudget.rawMulCoefficientBudget] using hmulShift
  have hscaleBound : ActualRawPowCoefficientBudget.rawMulCoefficientBudget
      (CPolynomial.Raw.C p.leadingCoeff) shiftedQ ≤
      1 * (2 * N + 2) + 1 * (1 + (2 * N + 2)) + (1 + (2 * N + 2)) := by
    simpa only [ActualRawPowCoefficientBudget.rawMulCoefficientBudget] using hmulScale
  have htermBound : ActualRawPowCoefficientBudget.rawMulCoefficientBudget
      (CPolynomial.Raw.C p.leadingCoeff) xShift ≤
      1 * (N + 1) + 1 * (1 + (N + 1)) + (1 + (N + 1)) := by
    simpa only [ActualRawPowCoefficientBudget.rawMulCoefficientBudget] using hmulTerm
  have hsubBound : scaledQ.size + 2 * max p.size scaledQ.size + max p.size scaledQ.size ≤
      (2 * N + 4) + 2 * (2 * N + 4) + (2 * N + 4) := by omega
  have haddBound : 2 * max quotientTail.size quotientTerm.size ≤ 2 * (N + 3) := by omega
  have hcost : ActualRawLongDivisionCostV2.activeDivisionStepBudget p q quotientTail ≤
      12 * N * (N + 1) +
      (N * (N + 1) + N * (N + (N + 1)) + (N + (N + 1))) +
      (1 * (2 * N + 2) + 1 * (1 + (2 * N + 2)) + (1 + (2 * N + 2))) +
      ((2 * N + 4) + 2 * (2 * N + 4) + (2 * N + 4)) +
      12 * N * (N + 1) +
      (1 * (N + 1) + 1 * (1 + (N + 1)) + (1 + (N + 1))) +
      2 * (N + 3) := by
    rw [ActualRawLongDivisionCostV2.activeDivisionStepBudget_expanded]
    dsimp only
    have h1 := Nat.add_le_add hpowActual hshiftBound
    have h2 := Nat.add_le_add h1 hscaleBound
    have h3 := Nat.add_le_add h2 hsubBound
    have h4 := Nat.add_le_add h3 hpowActual
    have h5 := Nat.add_le_add h4 htermBound
    exact Nat.add_le_add h5 haddBound
  calc
    _ ≤ 12 * N * (N + 1) +
      (N * (N + 1) + N * (N + (N + 1)) + (N + (N + 1))) +
      (1 * (2 * N + 2) + 1 * (1 + (2 * N + 2)) + (1 + (2 * N + 2))) +
      ((2 * N + 4) + 2 * (2 * N + 4) + (2 * N + 4)) +
      12 * N * (N + 1) +
      (1 * (N + 1) + 1 * (1 + (N + 1)) + (1 + (N + 1))) +
      2 * (N + 3) := hcost
    _ ≤ 100 * (N + 3) * (N + 3) := by
      ring_nf
      omega

#print axioms active_step_budget_le
end ActualDivisionStepCostBound
