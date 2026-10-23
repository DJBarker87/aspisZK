import S9FinalPartsSourceTraceV1
import S9ActualSharedParentPartsCanonicalV1
import S9ActualUnsharedParentPartsCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FinalPartsSourceTraceV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev Good := AspisR1S9ActualFinalSumV1.Good
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
private theorem assembly_good (partials : Array W 4#usize) (self : weights.Weights)
    (ap0 ap1 : Powers) (parts out : Parts)
    (h : AspisR1S9SharedHighScalarAssemblyV1.Assembly partials self ap0 ap1 parts out) : Good out := by
  rcases h with ⟨row0,row2,high0,high2,f00,f01,f20,f21,dot0,dot2,s00,s01,s20,s21,
    scale0,scale2,product0,product2,h⟩
  repeat' first | exact h.1 | rcases h with ⟨_,h⟩


theorem shared_trace_final_canonical (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (partsFinal : Parts) (k : Array W 7#usize)
    (hs2 : self.variant=transport.Variant.S2)
    (hfactors : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical self)
    (hextra : ∀ i q,Array.index_usize self.extra i=.ok q →
      AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (htrace : SharedTrace self alpha f kappa out partsFinal k) : Good partsFinal := by
  rcases htrace with ⟨_,_,_,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,partsShared,selfCommon,common,partials,low,inactive,partsInactive,useFactored,libra,hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hcommon,hpartials,hhigh,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩
  have hp0 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
    a0 ap0 (halpha 0#usize a0 ha0) hap0
  have hp1 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
    a1 ap1 (halpha 1#usize a1 ha1) hap1
  have hsame := AspisR1S9PairLoop1SelfComponentV3.pair_loop1_first_component
    {start:=0#usize,«end»:=16#usize} self selfCommon
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO) common hcommon
  subst selfCommon
  have creg := AspisR1S9RegularPartsCanonicalV1.regular_from_zero_success_good
    self true alpha f n ap0 ap1 scratch scratchOut partsRegular hs2 hp0 hp1 hregular
  have ashared := AspisR1S9SharedHighScalarAssemblyV1.shared_high_success_value_assembly
    partials self ap0 ap1 partsRegular partsShared hfactors hp0 hp1 creg hhigh
  have cshared := assembly_good partials self ap0 ap1 partsRegular partsShared ashared
  have clow := (AspisR1S9ActualLow16LoopMeaningV1.actual_shared_low_loop_success
    ap0 ap1 {start:=0#usize,«end»:=16#usize}
    (Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO) low
    hp0 hp1 rfl rfl hlow).2
  have cinactive := AspisR1S9S2InactiveCanonicalV1.s2_exact_span_dispatch_success_canonical
    self f low inactive hs2 hspan clow hinactive
  have cpartsInactive := AspisR1S9CanonicalPartsUpdateV1.update_preserves_good
    partsShared partsInactive 0#usize inactive (by decide) cshared cinactive hpartsInactive
  have heq : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant
      transport.Variant.S2=.ok true := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  have htrue : useFactored=true := Result.ok.inj (huse.symm.trans heq)
  subst useFactored
  simp only [↓reduceIte] at hlibra
  have cfinal := AspisR1S9FactoredActiveCanonicalV1.factored_active_success_canonical
    ap0 ap1 self.extra libra f partsInactive partsFinal hp0 hp1 hextra
    cpartsInactive hlibra hactive
  exact cfinal

theorem unshared_trace_final_canonical (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (partsFinal : Parts) (k : Array W 7#usize)
    (hs2 : self.variant=transport.Variant.S2)
    (hextra : ∀ i q,Array.index_usize self.extra i=.ok q →
      AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (htrace : UnsharedTrace self alpha f kappa out partsFinal k) : Good partsFinal := by
  rcases htrace with ⟨_,_,_,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,low,inactive,partsInactive,useFactored,libra,hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩
  have hp0 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
    a0 ap0 (halpha 0#usize a0 ha0) hap0
  have hp1 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
    a1 ap1 (halpha 1#usize a1 ha1) hap1
  have creg := AspisR1S9RegularPartsCanonicalV1.regular_from_zero_success_good
    self false alpha f n ap0 ap1 scratch scratchOut partsRegular hs2 hp0 hp1 hregular
  have clow := (AspisR1S9ActualLow16LoopMeaningV1.actual_low_loop_success
    ap0 ap1 {start:=0#usize,«end»:=16#usize}
    (Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO) low
    hp0 hp1 rfl rfl hlow).2
  have cinactive := AspisR1S9S2InactiveCanonicalV1.s2_exact_span_dispatch_success_canonical
    self f low inactive hs2 hspan clow hinactive
  have cpartsInactive := AspisR1S9CanonicalPartsUpdateV1.update_preserves_good
    partsRegular partsInactive 0#usize inactive (by decide) creg cinactive hpartsInactive
  have heq : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant
      transport.Variant.S2=.ok true := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  have htrue : useFactored=true := Result.ok.inj (huse.symm.trans heq)
  subst useFactored
  simp only [↓reduceIte] at hlibra
  have clibra := (AspisR1S9ActualPairHelperLoopToOldV1.actual_helper_success_to_old
    ap0 ap1 self.extra libra hp0 hp1 hextra hlibra).1
  have cfinal := AspisR1S9ActiveFourCanonicalV1.unshared_active_success_canonical
    f libra {start:=0#usize,«end»:=4#usize} partsInactive partsFinal cpartsInactive clibra hactive
  exact cfinal

#print axioms shared_trace_final_canonical
#print axioms unshared_trace_final_canonical
end AspisR1S9FinalPartsSourceTraceV1
