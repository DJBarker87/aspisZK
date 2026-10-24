import S9ConstructorV3CompleteFactorSemanticsV1
import S9StatementD18OpeningPointsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CompleteConstructorOpeningFactorsV1
open AspisR1S9ActualWeightsNewBoxNewV3
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3PointScanBodyCanonicalV1
open AspisR1S9ConstructorV3DecodedInputV1
abbrev Circles := AspisR1S9ConstructorV3CompleteFactorSemanticsV1.Circles

/-- COMPLETE accepted constructor statement factors in the EXISTING protocol
point model. Both phases and the SAME statement-point producer are derived
from this constructor call, not provided as independent premises. -/
theorem constructor_success_statement_opening_factors
    (variant : Variant) (alpha : Vector) (z : Circles) (w : Weights)
    (halpha : VectorCanonical alpha) (hz : PointsCanonical z)
    (hnew : weights_new variant alpha z = .ok (.Ok w)) :
    ∀ (k d i : Usize) (hk : k.val < 3) (hd : d.val < 5) (hi : i.val < 4),
      AspisR1S9FactorTableSemanticsV1.value w.factors k d i (by omega) hd hi =
      AspisR1.pairFactor
        (R0P.SemSource.openingPoints (fun j : Fin 10 => decodedInput alpha j.val)
          ⟨k.val,hk⟩
          ⟨2*(AspisR1.d18Tau ⟨d.val,hd⟩).val,
            by have ht := (AspisR1.d18Tau ⟨d.val,hd⟩).isLt; omega⟩)
        (R0P.SemSource.openingPoints (fun j : Fin 10 => decodedInput alpha j.val)
          ⟨k.val,hk⟩
          ⟨2*(AspisR1.d18Tau ⟨d.val,hd⟩).val+1,
            by have ht := (AspisR1.d18Tau ⟨d.val,hd⟩).isLt; omega⟩) i.val := by
  obtain ⟨model,hmeaning,hrows,hcircle,hpoints,hvariant,hextra⟩ :=
    AspisR1S9ConstructorV3CompleteFactorSemanticsV1.constructor_success_complete_factor_semantics
      variant alpha z w halpha hz hnew
  intro k d i hk hd hi
  have hk5 : k.val < 5 := by omega
  have hvalue := hmeaning k d i hk5 hd hi
  have hrow := hrows k d i hk hd hi hk
  have hmodel := AspisR1S9StatementD18OpeningPointsV1.expected_eq_openingPoints
    alpha w.points halpha hpoints ⟨k.val,hk⟩ d hd i.val
  exact hvalue.trans (hrow.trans hmodel)

#print axioms constructor_success_statement_opening_factors
end AspisR1S9CompleteConstructorOpeningFactorsV1
