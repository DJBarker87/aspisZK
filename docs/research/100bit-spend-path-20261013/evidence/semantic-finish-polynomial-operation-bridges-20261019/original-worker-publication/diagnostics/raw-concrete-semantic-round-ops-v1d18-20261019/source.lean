import ExtractedSemanticRoundsCheckedTrace
import RawSemanticArrayPolynomialOps

/-! A concrete Aeneas boundary/value adapter for decoded 28-field rows. The
record decoder remains explicit; the endpoint-sum and challenge evaluation
operations are fixed to the source-shaped fold and Horner implementation. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.RawConcreteSemanticRoundOps
open RawSemanticArrayPolynomialOps

abbrev RowDecoder :=
  (N : Usize) → r1_wire.ValidatedRecord → Usize →
    Result (core.result.Result (Array aspis_core.field.QM31 N) r1_wire.Error)

def boundaries (decode : RowDecoder) : RoundModel.Boundaries where
  decode := decode
  boundary := fun polynomial => ok (decodedBoundary polynomial)
  value := fun polynomial alpha round => do
    let challenge ← Array.index_usize alpha round
    ok (decodedValue polynomial challenge)

theorem boundary_is_polynomial_endpoint_sum
    (decode : RowDecoder) (polynomial : Array aspis_core.field.QM31 28#usize) :
    boundaries decode |>.boundary polynomial =
      ok ((decodedPolynomial polynomial).eval 0 + (decodedPolynomial polynomial).eval 1) := by
  simp only [boundaries, decodedBoundary_eq_endpoint_sum]

theorem value_is_polynomial_eval
    (decode : RowDecoder) (polynomial : Array aspis_core.field.QM31 28#usize)
    (alpha : Array aspis_core.field.QM31 10#usize) (round : Usize)
    (challenge : aspis_core.field.QM31)
    (hget : Array.index_usize alpha round = ok challenge) :
    boundaries decode |>.value polynomial alpha round =
      ok ((decodedPolynomial polynomial).eval challenge) := by
  simp only [boundaries, hget, bind_tc_ok, decodedValue_eq_polynomial_eval]

#print axioms boundary_is_polynomial_endpoint_sum
#print axioms value_is_polynomial_eval

end AspisR1PublicPreparation.RawConcreteSemanticRoundOps
