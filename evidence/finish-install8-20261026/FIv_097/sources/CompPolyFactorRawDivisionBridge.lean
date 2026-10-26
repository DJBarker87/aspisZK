import ActualLongDivisionTotalCostV2
import CompPolyFactorTotalDivisionCost
import CompPolySplitFactorQuality
import Lean.Elab.Tactic.Omega

/-! Connect the high-level recursive `CPolynomial.divByMonic` call to the
costed Raw long-division mirror. In pinned CompPoly 4165a87, CPolynomial's
implementation applies `Raw.divByMonic` to its stored `val` arrays, and Raw
division projects the quotient from `Raw.divModByMonicAux`.
-/
namespace AspisR1.CompPolyFactorRawDivisionBridge
open CompPoly AspisR1.CompPolySplitRetries AspisR1.CompPolySplitFactorQuality

def actualDivisionCharge {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
    (f d : CPolynomial K) : Nat :=
  (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost
    f.val.size f.val d.val).2

/-- The right-child input in `factor` is the quotient of this exact costed
Raw execution, not merely a polynomial with the same denotation. -/
theorem divByMonic_value_eq_costed_raw
    {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
    (f d : CPolynomial K) :
    (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost
      f.val.size f.val d.val).1.1 = (f.divByMonic d).val := by
  rw [ActualRawLongDivisionCostV2.divModByMonicWithCost_value]
  rfl

private theorem monic_leadingCoeff_eq_one
    {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (f : CPolynomial K) (hf : f.toPoly.Monic) : f.leadingCoeff = 1 := by
  have hm : f.monic := (CPolynomial.monic_toPoly_iff f).2 hf
  have hb : f.leadingCoeff == 1 := by simpa [CPolynomial.monic] using hm
  exact beq_iff_eq.mp hb

private theorem monic_val_size_eq_degree_succ
    {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (f : CPolynomial K) (hf : f.toPoly.Monic) :
    f.val.size = f.toPoly.natDegree + 1 := by
  have hlead := monic_leadingCoeff_eq_one f hf
  have hpos : 0 < f.val.size := by
    by_contra hz
    have hz' : f.val.size = 0 := by omega
    have hfalse : (0 : K) = 1 := by
      simpa [CPolynomial.leadingCoeff, Array.getLastD, hz'] using hlead
    exact (zero_ne_one hfalse)
  have hnat : f.natDegree = f.toPoly.natDegree := CPolynomial.natDegree_toPoly f
  cases hs : f.val.size with
  | zero => simp [hs] at hpos
  | succ n =>
      have hnat' : n = f.toPoly.natDegree := by
        simpa [CPolynomial.natDegree, hs] using hnat
      rw [hnat']

private theorem raw_leadingCoeff_eq_one
    {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (f : CPolynomial K) (hf : f.toPoly.Monic) : f.val.leadingCoeff = 1 := by
  have hlead := monic_leadingCoeff_eq_one f hf
  simpa [CPolynomial.leadingCoeff, CPolynomial.Raw.leadingCoeff,
    CPolynomial.Raw.Trim.trim_eq_of_isCanonical f.property] using hlead

private theorem positive_raw_size_of_monic
    {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (f : CPolynomial K) (hf : f.toPoly.Monic) : 0 < f.val.size := by
  have := monic_val_size_eq_degree_succ f hf
  omega

private theorem poly_charge_monotone (x D : Nat) (hx : x ≤ D+1) :
    x * (100 * (x+4) * (x+4)) ≤
      (D+1) * (100 * (D+5) * (D+5)) := by
  have hshift : x+4 ≤ D+5 := by omega
  have hscaledLeft : 100 * (x+4) ≤ 100 * (D+5) :=
    Nat.mul_le_mul_left 100 hshift
  have hscaled : 100 * (x+4) * (x+4) ≤ 100 * (D+5) * (D+5) :=
    Nat.mul_le_mul hscaledLeft hshift
  exact Nat.mul_le_mul hx hscaled

/-- At every successful split, the actual raw division charge is cubic in
the parent degree. Both raw operands are the stored arrays; canonicality
provides trimming, and the accepted divisor is monic and nonempty. -/
theorem actualDivisionCharge_le_degree_bound
    {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]
    (q t node D : Nat) (coins : Nat → Fin t → K × K)
    (f d : CPolynomial K) (hf : f.toPoly.Monic)
    (hdegree : f.toPoly.natDegree ≤ D)
    (hsplit : retry f q t (coins node) = some d) :
    actualDivisionCharge f d ≤ (D+1) * (100 * (D+5) * (D+5)) := by
  have hd := retry_quality f d q t (coins node) hf hsplit
  have hpTrim : f.val.trim = f.val :=
    CPolynomial.Raw.Trim.trim_eq_of_isCanonical f.property
  have hqTrim : d.val.trim = d.val :=
    CPolynomial.Raw.Trim.trim_eq_of_isCanonical d.property
  have hqMonic : d.val.leadingCoeff = 1 := raw_leadingCoeff_eq_one d hd.1
  have hqpos : 0 < d.val.size := positive_raw_size_of_monic d hd.1
  have hpsize : f.val.size ≤ D+1 := by
    rw [monic_val_size_eq_degree_succ f hf]
    omega
  have hraw := ActualLongDivisionTotalCostV1.public_division_total_cost
    f.val d.val hpTrim hqTrim hqMonic hqpos
  unfold actualDivisionCharge
  exact hraw.trans (poly_charge_monotone f.val.size D hpsize)

/-- Whole-factor aggregation for the exact charge above is quartic in the
root degree. Retry sampling calls are separately bounded by the existing
`actual_retry_calls_le_degree` theorem. -/
theorem actual_factor_division_cost_le
    {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]
    (q t fuel node : Nat) (coins : Nat → Fin t → K × K)
    (f : CPolynomial K) (hf : f.toPoly.Monic) :
    (AspisR1.CompPolyFactorTotalDivisionCost.factorCosted q t coins
      actualDivisionCharge fuel node f).2 ≤
      (f.toPoly.natDegree-1) *
        ((f.toPoly.natDegree+1) *
          (100 * (f.toPoly.natDegree+5) * (f.toPoly.natDegree+5))) := by
  exact AspisR1.CompPolyFactorTotalDivisionCost.factorCosted_total_le_degree_mul
      (q := q) (t := t) (coins := coins) (charge := actualDivisionCharge)
      (B := (f.toPoly.natDegree+1) *
        (100 * (f.toPoly.natDegree+5) * (f.toPoly.natDegree+5)))
      (D := f.toPoly.natDegree)
      (hcharge := by
        intro node' g d hg hdeg hs
        exact actualDivisionCharge_le_degree_bound q t node' f.toPoly.natDegree
          coins g d hg hdeg hs)
      (fuel := fuel) (node := node) (f := f) hf le_rfl

#print axioms divByMonic_value_eq_costed_raw
#print axioms actualDivisionCharge_le_degree_bound
#print axioms actual_factor_division_cost_le
end AspisR1.CompPolyFactorRawDivisionBridge
