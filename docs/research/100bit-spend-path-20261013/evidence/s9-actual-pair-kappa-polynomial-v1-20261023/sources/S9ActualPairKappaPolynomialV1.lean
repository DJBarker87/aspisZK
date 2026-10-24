import S9ActualSharedPairKappaPolynomialV1
import S9ActualUnsharedPairKappaPolynomialV1
import S9ActualPairRegularPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualPairKappaPolynomialV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
/-- Actual accepted Pair selects its own source branch. No premise about
which branch it took, intermediate success, powers, or final parts remains.
Caller S2/receiver/alpha/kappa/span guards and parts-to-relation meaning
remain explicit; this is not a complete spend soundness theorem. -/
theorem actual_pair_returns_own_kappa_polynomial
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hs2 : self.variant=transport.Variant.S2)
    (hfactors : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical self)
    (hextra : ∀ i q,Array.index_usize self.extra i=.ok q →
      AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hfold : Slice.len alpha=2#usize)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (hpair : weights.Weights.pair self alpha f kappa=.ok (.Ok out))
    (hkappa : Can kappa) :
    ∃ parts : Parts, AspisR1S9ActualFinalSumV1.Good parts ∧ Can out ∧
      AspisR1S9NativeWideDecodedArithmeticV1.decode out=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial parts kappa := by
  obtain ⟨n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
    hn,hexpected,hparse,ha0,hap0,ha1,hap1,hreserve,hguard,hregular⟩ :=
    AspisR1S9ActualPairRegularPrefixV1.actual_pair_success_regular_prefix
      self alpha f kappa out hfold hpair
  cases shared with
  | true =>
    exact AspisR1S9ActualSharedPairKappaPolynomialV1.actual_shared_pair_returns_kappa_polynomial
      self alpha f kappa out hs2 hfactors hextra halpha hfold hspan hguard hpair hkappa
  | false =>
    exact AspisR1S9ActualUnsharedPairKappaPolynomialV1.actual_unshared_pair_returns_kappa_polynomial
      self alpha f kappa out hs2 hextra halpha hfold hspan hguard hpair hkappa
#print axioms actual_pair_returns_own_kappa_polynomial
end AspisR1S9ActualPairKappaPolynomialV1
