import S9SourceQuarterInverseV1
import RoundPairing
set_option autoImplicit false
namespace AspisR1S9SourceQuarterModelBridgeV1
open AspisR1S9ProductionPairCutV1
abbrev M := AspisR1CurrentWide.Proof.MExact
abbrev E := AspisWideTower.WideExact

/-- The existing mapped-inverse proof is reused on ABSTRACT fields; the model
quarter is exposed there, before specializing any concrete inverse/numeral. -/
theorem mapped_model_quarter {A B : Type} [CommRing A] [Field B]
    (iota : A →+* B) (q : A) (h : q*(4 : A)=1) :
    iota q=(AspisR1.RoundPairing.quarter : B) := by
  change iota q=(4 : B)⁻¹
  have hb := congrArg iota h
  rw [map_mul,map_one,map_ofNat] at hb
  have hn : (4 : B)≠0 := by
    intro hz
    rw [hz,mul_zero] at hb
    exact zero_ne_one hb
  calc
    _ = iota q*((4 : B)*(4 : B)⁻¹) := by rw [mul_inv_cancel₀ hn,mul_one]
    _ = (iota q*(4 : B))*(4 : B)⁻¹ := (mul_assoc _ _ _).symm
    _ = _ := by rw [hb,one_mul]

/-- SAME source quarter and existing source prime-field product law. No
concrete E inverse4 is created in a hypothesis or intermediate proposition. -/
theorem source_quarter_eq_model_quarter :
    AspisR1S9ScalarActualPowerPolynomialV1.quarter=
      (AspisR1.RoundPairing.quarter : E) := by
  exact (AspisR1CurrentWide.Proof.wideScalarEmbedding_eq_algebraMap weights.QUARTER).trans
    (mapped_model_quarter (algebraMap M E)
      (R17CurrentM31Semantics.decode weights.QUARTER)
      AspisR1S9SourceQuarterInverseV1.base_quarter_mul_four)

#print axioms mapped_model_quarter
#print axioms source_quarter_eq_model_quarter
end AspisR1S9SourceQuarterModelBridgeV1
