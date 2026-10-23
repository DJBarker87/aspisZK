import S9ActiveOriginalCoefficientsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActiveOriginalCoefficientsBoundV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActiveOriginalCoefficientsV1 (A Q cells)
open AspisR1S9NativeS3WeightBodyV1 (decode)
open AspisR1S9ActualPairOldCarrierScalarV1 (toHelperW toHelperQ)
open AspisR1S9CandidateFoldMapPrimitivesV1 (mapArray)

/-- Source coefficient equation with caller-chosen phantom length evidence.
The old accepted API is unchanged; no data or mathematical premise is added. -/
theorem actual_helper_native_original_coefficients_bound
    (h4 : 4≤UScalar.cMax .Usize) (ap0 ap1 : A) (extra : Array Q 2#usize) (libra : A)
    (hp0 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0)
    (hp1 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1)
    (he : ∀ i q,Array.index_usize extra i=.ok q → AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (h : weights.factored_s2_libra_weights ap0 ap1 extra=.ok libra) :
    AspisR1S9ActualPairScalarCallbackV1.GoodArray libra ∧ ∃ q0 q1 : Q,
      Array.index_usize extra 0#usize=.ok q0 ∧ Array.index_usize extra 1#usize=.ok q1 ∧
      ∀ j : Fin 4,decode (cells libra j)=AspisR1.S2LibraFactoredIdentity.original
        (AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase
          (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap0))
        (AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase
          (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap1))
        (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
        (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1)) j := by
  obtain ⟨clibra,q0,q1,hq0,hq1,hvalues⟩ :=
    AspisR1S9ActiveOriginalCoefficientsV1.actual_helper_native_original_coefficients
      ap0 ap1 extra libra hp0 hp1 he h
  refine ⟨clibra,q0,q1,hq0,hq1,?_⟩
  intro j
  simpa only [mapArray] using hvalues j

#print axioms actual_helper_native_original_coefficients_bound
end AspisR1S9ActiveOriginalCoefficientsBoundV1
