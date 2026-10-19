import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness

open CompPoly
open CompPoly.CBivariate
open CompPoly.GuruswamiSudan

namespace AspisWide.GSInterpolationAgreementCore

/-- A real multiplicity-three interpolation witness and enough agreement at
its distinct packed abscissae force the evaluated univariate polynomial to
vanish. This is the existing CompPoly root-count theorem, exposed in the
polynomial representation consumed by the extractor. -/
theorem valid_witness_agreement_forces_eval_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    {Q : CBivariate F} {p : CPolynomial F}
    (hQ : ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound <
      params.multiplicity * matchingPointCount points p) :
    (CBivariate.toPoly Q).eval p.toPoly = 0 := by
  have hcompose := composeY_eq_zero_of_enough_matching_multiplicity_points
    hQ hpdeg hdistinct hmatches
  have hcomposePoly : (CBivariate.composeY Q p).toPoly = 0 :=
    (CPolynomial.toPoly_eq_zero_iff _).2 hcompose
  simpa only [composeY_toPoly] using hcomposePoly

#print axioms valid_witness_agreement_forces_eval_zero

end AspisWide.GSInterpolationAgreementCore
