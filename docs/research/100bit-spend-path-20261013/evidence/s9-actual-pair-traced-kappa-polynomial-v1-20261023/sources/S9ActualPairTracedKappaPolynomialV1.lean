import S9FinalPartsSourceTraceCanonicalV1
import S9ActualKappaFinalSumV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FinalPartsSourceTraceV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
/-- The exact SAME source-chosen final parts and kappa array remain linked to
all source phase events in the exported statement. No loose existential
array with merely the desired polynomial equation is substituted. -/
theorem actual_pair_traced_kappa_polynomial
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
    ∃ partsFinal k, Trace self alpha f kappa out partsFinal k ∧ Good partsFinal ∧ Can out ∧
      AspisR1S9NativeWideDecodedArithmeticV1.decode out=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial partsFinal kappa := by
  obtain ⟨n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
    hn,hexpected,hparse,ha0,hap0,ha1,hap1,hreserve,hguard,hregular⟩ :=
    AspisR1S9ActualPairRegularPrefixV1.actual_pair_success_regular_prefix
      self alpha f kappa out hfold hpair
  cases shared with
  | true =>
    obtain ⟨partsFinal,k,ht⟩ := shared_trace_of_pair self alpha f kappa out hfold hguard hpair
    have hc := shared_trace_final_canonical self alpha f kappa out partsFinal k
      hs2 hfactors hextra halpha hspan ht
    have htcopy := ht
    rcases htcopy with ⟨_,_,_,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,partsShared,selfCommon,common,partials,low,inactive,partsInactive,useFactored,libra,hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hcommon,hpartials,hhigh,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩
    obtain ⟨hout,hpoly⟩ := AspisR1S9ActualKappaFinalSumV1.actual_shared_final_sum_is_kappa_polynomial
      partsFinal k kappa out hkappa hc hk hsum
    exact ⟨partsFinal,k,Or.inl ht,hc,hout,hpoly⟩
  | false =>
    obtain ⟨partsFinal,k,ht⟩ := unshared_trace_of_pair self alpha f kappa out hfold hguard hpair
    have hc := unshared_trace_final_canonical self alpha f kappa out partsFinal k
      hs2 hextra halpha hspan ht
    have htcopy := ht
    rcases htcopy with ⟨_,_,_,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,low,inactive,partsInactive,useFactored,libra,hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩
    obtain ⟨hout,hpoly⟩ := AspisR1S9ActualKappaFinalSumV1.actual_final_sum_is_kappa_polynomial
      partsFinal k kappa out hkappa hc hk hsum
    exact ⟨partsFinal,k,Or.inr ht,hc,hout,hpoly⟩

#print axioms actual_pair_traced_kappa_polynomial
end AspisR1S9FinalPartsSourceTraceV1
