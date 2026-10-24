import S9ActualLowModelWeightV1
import S9ActiveOriginalCoefficientsV1
import S9TwoDualSourcePrivateV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9PrivateScaledBaseModelV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActiveOriginalCoefficientsV1 (A cells trace_decode_native mapped_helper_cells)
open AspisR1S9ActualPairOldCarrierScalarV1 (toHelperW)
open AspisR1S9CandidateFoldMapPrimitivesV1 (mapArray)
open AspisR1S9WideFieldOperatorBridgesV1 (fieldPow pow_operator_eq)
abbrev E := AspisWideTower.WideExact

theorem generic_powers_api {K : Type} [Field K] (a : K) (r : Fin 4) :
    AspisR1S9TwoDualSourceBaseV1.powers a r=fieldPow a r.val := rfl

/-- Pointwise actual powers observation, before any ORIGINAL finite sum is
specialized. Length evidence is threaded from its source API. -/
theorem actual_mapped_base_power (h4 : 4≤UScalar.cMax .Usize)
    (x : W) (ap : A) (hx : Can x) (hp : weights.powers 4#usize x=.ok ap) (r : Fin 4) :
    AspisR1S9BodyPrefixPolynomialSumsV1.Base
      (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap) r=
      AspisR1S9TwoDualSourceBaseV1.powers (decode x) r := by
  have hmap : AspisR1S9ActualPairHelperOriginalCoefficientsV1.cells
      (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap) r=toHelperW (cells ap r) := by
    simpa only [mapArray] using mapped_helper_cells ap r
  change AspisR1S9ActualPairHelperOriginalCoefficientsV1.TraceDecode
    (AspisR1S9ActualPairHelperOriginalCoefficientsV1.cells
      (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap) r)=_
  rw [hmap,trace_decode_native]
  have hv := AspisR1S9ActualLowGenericWeightV1.actual_power_value x ap hx hp r.val r.isLt
  have hcell : AspisR1S9ActualLow16BodyMeaningV1.powerValue ap r.val=decode (cells ap r) := by
    unfold AspisR1S9ActualLow16BodyMeaningV1.powerValue cells
    rw [List.getElem?_eq_getElem (by simpa [ap.property] using r.isLt)]
  have hpow := pow_operator_eq (decode x) r.val
  have hgeneric := generic_powers_api (decode x) r
  exact hcell.symm.trans (hv.trans (hpow.trans hgeneric.symm))

/-- Compare source U32 constants before embedding; no wide value is reduced. -/
theorem helper_quarter_word_same : AspisR1S9HelperP6.weights.QUARTER=weights.QUARTER := by
  unfold AspisR1S9HelperP6.weights.QUARTER weights.QUARTER
  rfl

theorem helper_quarter_model :
    AspisR1S9BodyPrefixPolynomialSumsV1.Quarter=(AspisR1.RoundPairing.quarter : E) := by
  have hword := congrArg AspisR1CurrentWide.Proof.wideScalarEmbedding helper_quarter_word_same
  exact hword.trans AspisR1S9ActualLowModelWeightV1.low_source_quarter_eq_model

/-- ScaledBase is the existing generic PERM-scaled decoded challenge powers,
with the actual quarter identity discharged. No ORIGINAL algebra is repeated. -/
theorem actual_scaled_base_model (h4 : 4≤UScalar.cMax .Usize)
    (x : W) (ap : A) (hx : Can x) (hp : weights.powers 4#usize x=.ok ap) :
    AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase
      (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap)=
      AspisR1.S2LibraFactoredIdentity.scaled
        (AspisR1S9TwoDualSourceBaseV1.powers (decode x)) AspisR1.RoundPairing.quarter := by
  have hb : AspisR1S9BodyPrefixPolynomialSumsV1.Base
      (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap)=
      AspisR1S9TwoDualSourceBaseV1.powers (decode x) := by
    funext r
    exact actual_mapped_base_power h4 x ap hx hp r
  exact congrArg₂ AspisR1.S2LibraFactoredIdentity.scaled hb helper_quarter_model

#print axioms generic_powers_api
#print axioms actual_mapped_base_power
#print axioms helper_quarter_word_same
#print axioms helper_quarter_model
#print axioms actual_scaled_base_model
end AspisR1S9PrivateScaledBaseModelV1
end
