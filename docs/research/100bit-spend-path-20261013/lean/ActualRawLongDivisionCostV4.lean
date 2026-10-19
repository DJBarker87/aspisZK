import ActualRawPowCoefficientBudget
import CompPoly.Univariate.Raw.Proofs
import Lean.Elab.Tactic.Omega

namespace ActualRawLongDivisionCostV2
open CompPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

private def addBudget (p q : CPolynomial.Raw F) : Nat :=
  2 * max p.size q.size

private def subAndTrimBudget (p q : CPolynomial.Raw F) : Nat :=
  q.size + addBudget p q + max p.size q.size

/-- Charge the exact operations in one active branch of Raw.divModByMonicAux:
two linear Raw.pow calls for the shifts, the two naive multiplications forming
the cancellation term, subtraction and its two trims, then the quotient
addition and trim.  The operands are the actual intermediate raw arrays. -/
def activeDivisionStepBudget (p q : CPolynomial.Raw F)
    (quotientTail : CPolynomial.Raw F) : Nat :=
  let k := p.size - q.size
  let xShift := (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k
  let shiftedQ := q * xShift
  let scaledQ := CPolynomial.Raw.C p.leadingCoeff * shiftedQ
  let quotientTerm := CPolynomial.Raw.C p.leadingCoeff *
    ((CPolynomial.Raw.X : CPolynomial.Raw F) ^ k)
  let powBudget := (ActualRawPowCoefficientBudget.rawPowWithCoefficientBudget
      (CPolynomial.Raw.X : CPolynomial.Raw F) k).2
  let shiftMulBudget := ActualRawPowCoefficientBudget.rawMulCoefficientBudget q xShift
  let scaleMulBudget := ActualRawPowCoefficientBudget.rawMulCoefficientBudget
    (CPolynomial.Raw.C p.leadingCoeff) shiftedQ
  let quotientMulBudget := ActualRawPowCoefficientBudget.rawMulCoefficientBudget
    (CPolynomial.Raw.C p.leadingCoeff) xShift
  powBudget + shiftMulBudget + scaleMulBudget + subAndTrimBudget p scaledQ +
    powBudget + quotientMulBudget + addBudget quotientTail quotientTerm

/-- A cost-annotated mirror of the pinned recursive long-division function.
Its value component follows the same fuel, branch, intermediate arrays, and
quotient accumulation as `Raw.divModByMonicAux.go`. -/
def divModByMonicAuxWithCost : Nat → CPolynomial.Raw F → CPolynomial.Raw F →
    (CPolynomial.Raw F × CPolynomial.Raw F) × Nat
  | 0, p, _ => ((0, p), 0)
  | n + 1, p, q =>
      if p.size < q.size then
        ((0, p), 0)
      else
        let k := p.size - q.size
        let q' := CPolynomial.Raw.C p.leadingCoeff *
          (q * (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k)
        let p' := (p - q').trim
        let tail := divModByMonicAuxWithCost n p' q
        let quotientTerm := CPolynomial.Raw.C p.leadingCoeff *
          (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k
        ((tail.1.1 + quotientTerm, tail.1.2),
          tail.2 + activeDivisionStepBudget p q tail.1.1)
termination_by fuel _ _ => fuel

theorem divModByMonicAuxWithCost_value (fuel : Nat)
    (p q : CPolynomial.Raw F) :
    (divModByMonicAuxWithCost fuel p q).1 =
      CPolynomial.Raw.divModByMonicAux.go fuel p q := by
  induction fuel generalizing p with
  | zero => simp [divModByMonicAuxWithCost, CPolynomial.Raw.divModByMonicAux.go]
  | succ fuel ih =>
      unfold divModByMonicAuxWithCost CPolynomial.Raw.divModByMonicAux.go
      by_cases h : p.size < q.size
      · simp [h]
      · simp only [h, ↓reduceIte]
        rw [ih]
        simp only [HPow.hPow, Pow.pow]

/-- The complete costed computation refines the actual pinned quotient and
remainder; the wrapper uses the implementation's own initial `p.size` fuel. -/
theorem divModByMonicWithCost_value (p q : CPolynomial.Raw F) :
    (divModByMonicAuxWithCost p.size p q).1 =
      CPolynomial.Raw.divModByMonicAux p q := by
  simpa [CPolynomial.Raw.divModByMonicAux] using
    divModByMonicAuxWithCost_value p.size p q

#print axioms divModByMonicAuxWithCost_value
#print axioms divModByMonicWithCost_value
/-- Exact public expansion of the active-branch coefficient charge. -/
theorem activeDivisionStepBudget_expanded (p q quotientTail : CPolynomial.Raw F) :
    activeDivisionStepBudget p q quotientTail =
      let k := p.size - q.size
      let xShift := (CPolynomial.Raw.X : CPolynomial.Raw F) ^ k
      let shiftedQ := q * xShift
      let scaledQ := CPolynomial.Raw.C p.leadingCoeff * shiftedQ
      let quotientTerm := CPolynomial.Raw.C p.leadingCoeff * xShift
      let powBudget := (ActualRawPowCoefficientBudget.rawPowWithCoefficientBudget
          (CPolynomial.Raw.X : CPolynomial.Raw F) k).2
      let shiftMulBudget := ActualRawPowCoefficientBudget.rawMulCoefficientBudget q xShift
      let scaleMulBudget := ActualRawPowCoefficientBudget.rawMulCoefficientBudget
        (CPolynomial.Raw.C p.leadingCoeff) shiftedQ
      let quotientMulBudget := ActualRawPowCoefficientBudget.rawMulCoefficientBudget
        (CPolynomial.Raw.C p.leadingCoeff) xShift
      powBudget + shiftMulBudget + scaleMulBudget +
        ((scaledQ.size + 2 * max p.size scaledQ.size) + max p.size scaledQ.size) +
        powBudget + quotientMulBudget + 2 * max quotientTail.size quotientTerm.size := by
  unfold activeDivisionStepBudget subAndTrimBudget addBudget
  rfl

#print axioms activeDivisionStepBudget_expanded
end ActualRawLongDivisionCostV2
