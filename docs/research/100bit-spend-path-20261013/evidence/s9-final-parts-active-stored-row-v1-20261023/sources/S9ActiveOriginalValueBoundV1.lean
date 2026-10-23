import S9ActiveOriginalCoefficientsBoundV1
import S9ActiveFourValueLoopV1
import S9ActiveOriginalValueV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActiveOriginalValueBoundV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActiveFourCanonicalV1 (Parts Libra)
open AspisR1S9ActiveFourValueStepV1 (cell4 libraValue E)
open AspisR1S9ActiveOriginalCoefficientsV1 (cells Q)
open AspisR1S9ActualPairOldCarrierScalarV1 (toHelperW toHelperQ)
open AspisR1S9CandidateFoldMapPrimitivesV1 (mapArray)
open AspisR1S9NativeS3CoefficientBodyV1 (C)
open AspisR1S9ActiveFourValueLoopV1 (activePrefix)

open AspisR1S9ActiveOriginalValueV1 (libra_value_fin active_prefix_fin_sum)

/-- SAME actual helper and active4 source runs give the existing ORIGINAL
S2 coefficient dot product on the SAME strict64 input stream. Initial cell4
is arbitrary/canonical; the caller's zero frame removes its additive term. -/
theorem actual_active_original_four_term_bound (h4 : 4≤UScalar.cMax .Usize) (f : Slice U8) (coefficients : C)
    (hbytes : 2048≤f.val.length)
    (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
    (ap0 ap1 : Libra) (extra : Array Q 2#usize) (libra : Libra) (initial final : Parts)
    (hp0 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0)
    (hp1 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1)
    (he : ∀ i q,Array.index_usize extra i=.ok q → AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (hhelper : weights.factored_s2_libra_weights ap0 ap1 extra=.ok libra)
    (hcarry : Can (cell4 initial))
    (hloop : weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} f initial libra=.ok final) :
    ∃ q0 q1 : Q,Array.index_usize extra 0#usize=.ok q0 ∧ Array.index_usize extra 1#usize=.ok q1 ∧
      Can (cell4 final) ∧ decode (cell4 final)=decode (cell4 initial)+
      ∑j : Fin 4,AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff j.val *
        AspisR1.S2LibraFactoredIdentity.original
          (AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap0))
          (AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap1))
          (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
          (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1)) j := by
  obtain ⟨clibra,q0,q1,hq0,hq1,hvalues⟩ :=
    AspisR1S9ActiveOriginalCoefficientsBoundV1.actual_helper_native_original_coefficients_bound
      h4 ap0 ap1 extra libra hp0 hp1 he hhelper
  obtain ⟨cfinal,hvalue⟩ := AspisR1S9ActiveFourValueLoopV1.active_loop_same_input_prefix
    f coefficients hbytes hcoeff libra initial final hcarry clibra hloop
  rw [active_prefix_fin_sum] at hvalue
  have hsum : (∑j : Fin 4,AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff j.val *
      libraValue libra j.val)=
      ∑j : Fin 4,AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff j.val *
        AspisR1.S2LibraFactoredIdentity.original
          (AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap0))
          (AspisR1S9ActualPairHelperOriginalCoefficientsV1.ScaledBase (@mapArray _ _ (Usize.ofNat 4 h4) toHelperW ap1))
          (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
          (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1)) j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [libra_value_fin,hvalues j]
  rw [hsum] at hvalue
  exact ⟨q0,q1,hq0,hq1,cfinal,hvalue⟩

#print axioms actual_active_original_four_term_bound
end AspisR1S9ActiveOriginalValueBoundV1
