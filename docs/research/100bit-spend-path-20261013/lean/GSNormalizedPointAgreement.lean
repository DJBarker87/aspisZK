import GSArrayMatchingCount
import CompPoly.Univariate.ToPoly.Impl

open CompPoly
open CompPoly.GuruswamiSudan

namespace AspisWide.GSNormalizedPointAgreement

def normalizedPoints {K : Type*} [Field K] {n : Nat}
    (points multipliers received : Fin n → K) : Array (K × K) :=
  Array.ofFn fun i => (points i, (multipliers i)⁻¹ * received i)

theorem matching_count_eq_agreement {K : Type*} [Field K] [BEq K]
    [LawfulBEq K] [DecidableEq K] {n : Nat}
    (points multipliers received encoder : Fin n → K)
    (p : CPolynomial K) (polyEval : Fin n → K)
    (heval : ∀ i, CPolynomial.eval (points i) p = polyEval i)
    (hmatch : ∀ i, polyEval i = (multipliers i)⁻¹ * received i ↔
      encoder i = received i) :
    matchingPointCount (normalizedPoints points multipliers received) p =
      (Finset.univ.filter fun i => received i = encoder i).card := by
  rw [normalizedPoints, AspisWide.GSArrayMatchingCount.matching_count_ofFn]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ((hmatch i).mp ((heval i).symm.trans h)).symm
  · intro h
    exact (heval i).trans ((hmatch i).mpr h.symm)

theorem normalized_points_distinct {K : Type*} [Field K] {n : Nat}
    (points multipliers received : Fin n → K)
    (hinj : Function.Injective points) :
    DistinctXCoordinates (normalizedPoints points multipliers received) := by
  simpa [DistinctXCoordinates, normalizedPoints, Function.comp_def] using
    (List.nodup_ofFn_ofInjective hinj)

#print axioms matching_count_eq_agreement
#print axioms normalized_points_distinct

end AspisWide.GSNormalizedPointAgreement
