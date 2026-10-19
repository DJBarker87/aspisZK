import ActualDivisionStepCostBoundV9
import PrivateDivStepBridgeV2
import RawMulSizeBoundV5
import Lean.Elab.Tactic.Omega

namespace ActualLongDivisionTotalCostV1
open CompPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

private theorem raw_add_size_le_max (p q : CPolynomial.Raw F) :
    (p + q).size ≤ max p.size q.size := by
  change (p.addRaw q).trim.size ≤ max p.size q.size
  exact (CPolynomial.Raw.Trim.size_le_size _).trans
    (le_of_eq (CPolynomial.Raw.add_size))

private theorem raw_C_mul_size_le (a : F) (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.C a * p).size ≤ p.size := by
  rw [CPolynomial.Raw.C_mul_eq_smul_trim]
  exact (CPolynomial.Raw.Trim.size_le_size _).trans (by simp [CPolynomial.Raw.smul])

private theorem xpow_size (k : Nat) :
    ((CPolynomial.Raw.X : CPolynomial.Raw F) ^ k).size = k + 1 :=
  ActualRawPowCoefficientBudget.rawXpow_size k

/-- Both arrays returned by any fuel prefix of the actual long-division mirror
remain no longer than the current dividend.  The quotient-tail bound is what
lets the exact active-step charge compose without assuming an output-size fact. -/
theorem output_sizes_le_dividend (fuel : Nat) (p q : CPolynomial.Raw F)
    (hp : p.trim = p) (hq : q.trim = q) (hm : q.leadingCoeff = 1)
    (hqpos : 0 < q.size) :
    (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p q).1.1.size ≤ p.size ∧
    (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p q).1.2.size ≤ p.size := by
  induction fuel generalizing p with
  | zero => simp [ActualRawLongDivisionCostV2.divModByMonicAuxWithCost]
  | succ fuel ih =>
      unfold ActualRawLongDivisionCostV2.divModByMonicAuxWithCost
      by_cases hstop : p.size < q.size
      · simp [hstop]
      · simp only [hstop, ↓reduceIte]
        let k := p.size - q.size
        let p' := (p - CPolynomial.Raw.C p.leadingCoeff *
          (q * (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k)).trim
        have hstep : p'.size < p.size := by
          simpa [p', k] using PrivateDivStepBridgeV2.monic_division_step_size_lt
            p q hp hq hm hstop hqpos
        have hp' : p'.trim = p' := by
          exact CPolynomial.Raw.Trim.trim_twice _
        have hrec := ih p' hp' 
        have hqtail :
            (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p' q).1.1.size ≤ p'.size := hrec.1
        have hrtail :
            (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p' q).1.2.size ≤ p'.size := hrec.2
        have hterm : (CPolynomial.Raw.C p.leadingCoeff *
            (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k).size ≤ p.size := by
          calc
            _ ≤ ((CPolynomial.Raw.X : CPolynomial.Raw F) ^ k).size := raw_C_mul_size_le _ _
            _ = k + 1 := xpow_size k
            _ ≤ p.size := by dsimp [k]; omega
        have hadd := raw_add_size_le_max
          (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p' q).1.1
          (CPolynomial.Raw.C p.leadingCoeff * (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k)
        constructor
        · exact hadd.trans (max_le (hqtail.trans hstep.le) hterm)
        · exact hrtail.trans hstep.le

/-- Total coefficient-operation charge of every fuel prefix, with an explicit
fixed array-size bound.  The exact active branch is charged by v9; terminal
branches contribute zero. -/
theorem total_cost_le_fuel_mul (fuel N : Nat) (p q : CPolynomial.Raw F)
    (hp : p.trim = p) (hq : q.trim = q) (hm : q.leadingCoeff = 1)
    (hqpos : 0 < q.size) (hsize : p.size ≤ N) (hN : 1 ≤ N) :
    (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p q).2 ≤
      fuel * (100 * (N + 3) * (N + 3)) := by
  induction fuel generalizing p with
  | zero => simp [ActualRawLongDivisionCostV2.divModByMonicAuxWithCost]
  | succ fuel ih =>
      unfold ActualRawLongDivisionCostV2.divModByMonicAuxWithCost
      by_cases hstop : p.size < q.size
      · simp [hstop]
      · simp only [hstop, ↓reduceIte]
        let k := p.size - q.size
        let p' := (p - CPolynomial.Raw.C p.leadingCoeff *
          (q * (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k)).trim
        have hstep : p'.size < p.size := by
          simpa [p', k] using PrivateDivStepBridgeV2.monic_division_step_size_lt
            p q hp hq hm hstop hqpos
        have hp' : p'.trim = p' := CPolynomial.Raw.Trim.trim_twice _
        have hrec := ih p' hp' (hstep.le.trans hsize)
        have htail :
            (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p' q).1.1.size ≤ N + 1 := by
          exact (output_sizes_le_dividend fuel p' q hp' hq hm hqpos).1.trans
            ((hstep.le.trans hsize).trans (Nat.le_succ N))
        have hstepCost := ActualDivisionStepCostBound.active_step_budget_le
          p q (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p' q).1.1
          N hN hsize (by omega) htail
        calc
          _ ≤ fuel * (100 * (N + 3) * (N + 3)) +
              100 * (N + 3) * (N + 3) := Nat.add_le_add hrec hstepCost
          _ = (fuel + 1) * (100 * (N + 3) * (N + 3)) := by
              rw [Nat.add_mul, Nat.one_mul]

/-- The actual public wrapper uses `p.size` fuel.  We pad the fixed bound by
one to cover the size-zero edge without a positivity assumption on p. -/
theorem public_division_total_cost (p q : CPolynomial.Raw F)
    (hp : p.trim = p) (hq : q.trim = q) (hm : q.leadingCoeff = 1)
    (hqpos : 0 < q.size) :
    (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost p.size p q).2 ≤
      p.size * (100 * (p.size + 4) * (p.size + 4)) := by
  exact total_cost_le_fuel_mul p.size (p.size + 1) p q hp hq hm hqpos
    (by omega) (by omega)

#print axioms output_sizes_le_dividend
#print axioms total_cost_le_fuel_mul
#print axioms public_division_total_cost
end ActualLongDivisionTotalCostV1
