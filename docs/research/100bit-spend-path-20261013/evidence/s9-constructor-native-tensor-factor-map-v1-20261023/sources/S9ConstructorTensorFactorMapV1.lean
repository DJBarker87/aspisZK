import S9ActualTensorStoredProductV1
import S9FinishActualConstructorSlotV1
import S9ConstructorV3QMMulSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorTensorFactorMapV1
open AspisR1S9FinishActualConstructorSlotV1
open AspisR1S9ActualTensorArithmeticV1 AspisR1S9ActualTensorStoredProductV1
abbrev CWeights := AspisR1S9ActualWeightsNewBoxNewV3.Weights

theorem native_ctor_decode (q : CQ) :
    decode (fromCtorQM q) = AspisR1S9ConstructorV3QMMulSemanticsV1.decode q := by
  rfl

theorem ctor_one_decode :
    AspisR1S9ConstructorV3QMMulSemanticsV1.decode
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE = 1 := by
  have he : fromCtorQM AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE =
      AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ONE := by
    unfold AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE
      AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ONE
    rfl
  rw [←native_ctor_decode,he]
  exact native_one_decode

def ctorStoredFactor (w : CWeights) (k d i : Nat) : ExactQM :=
  match w.factors.val[k]? with
  | none => 0
  | some row => match row.val[d]? with
    | none => 0
    | some coeffs => match coeffs.val[i]? with
      | none => 0
      | some q => AspisR1S9ConstructorV3QMMulSemanticsV1.decode q

/-- Structural correspondence of every stored factor, including failed lookup
positions. All nested constructor array coordinates are retained unchanged. -/
theorem native_stored_factor_from_constructor (w : CWeights) (k : Usize) (d i : Nat) :
    storedFactor (fromCtorWeights w) k d i = ctorStoredFactor w k.val d i := by
  unfold storedFactor fromCtorWeights mapArray AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
    ctorStoredFactor
  simp only [List.getElem?_map]
  cases hr : w.factors.val[k.val]? with
  | none => simp only [List.getElem?_map,hr,Option.map_none]
  | some row =>
    simp only [List.getElem?_map,hr,Option.map_some]
    cases hc : row.val[d]? with
    | none => simp only [List.getElem?_map,hc,Option.map_none]
    | some coeffs =>
      simp only [List.getElem?_map,hc,Option.map_some]
      cases hq : coeffs.val[i]? with
      | none => simp only [List.getElem?_map,hq,Option.map_none]
      | some q => simp only [List.getElem?_map,hq,Option.map_some,native_ctor_decode]

#print axioms ctor_one_decode
#print axioms native_ctor_decode
#print axioms native_stored_factor_from_constructor
end AspisR1S9ConstructorTensorFactorMapV1
