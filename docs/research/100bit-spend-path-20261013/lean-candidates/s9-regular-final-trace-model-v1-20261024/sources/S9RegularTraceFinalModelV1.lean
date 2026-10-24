import S9RegularPhaseConstructorModelV1
import S9FinalPartsSourceTraceV1
import S9SharedHighFrameV1
import S9ActiveFourFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9RegularTraceFinalModelV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
open AspisR1S9FactorArrayEntryV1
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
open AspisR1S9RegularPhaseConstructorModelV1 (Means)
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev Parts := AspisR1S9ActualProcessKindTensorReachedV1.Parts
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- SAME actual shared final trace and SAME final parts array. Real alpha
reads are retained; regular2/5/6 meanings survive actual shared1/3 writes,
then actual inactive0 and active4 writes. No independent phase success or
replacement final vector is supplied. -/
theorem shared_trace_final_regular_parts
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtor w))
    (hs2 : (fromCtor w).variant=transport.Variant.S2)
    (alpha : Slice NativeW) (f : Slice U8) (kappa out : NativeW)
    (partsFinal : Parts) (k : Array NativeW 7#usize)
    (halpha : ∀ (i : Usize) (a : NativeW),Slice.index_usize alpha i=.ok a → Can a)
    (htrace : AspisR1S9FinalPartsSourceTraceV1.SharedTrace
      (fromCtor w) alpha f kappa out partsFinal k) :
    ∃ a0 a1 : NativeW,
      Slice.index_usize alpha 0#usize=.ok a0 ∧ Slice.index_usize alpha 1#usize=.ok a1 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsFinal 2#usize (by decide) 1 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsFinal 5#usize (by decide) 3 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsFinal 6#usize (by decide) 4 := by
  obtain ⟨hfold,hguard,hpair,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,partsShared,
    selfCommon,common,partials,low,inactive,partsInactive,useFactored,libra,
    hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hcommon,hpartials,hhigh,
    hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩ := htrace
  have hregular' := hregular
  rw [hn64] at hregular'
  have hn' : (Slice.len f /32#usize : Result Usize)=.ok (64#usize) := by rw [←hn64];exact hn
  have hp := AspisR1S9RegularPhaseConstructorModelV1.actual_regular_phase_model_parts
    w model hm hc true alpha f a0 a1 (halpha 0#usize a0 ha0) (halpha 1#usize a1 ha1)
    ap0 ap1 hap0 hap1 scratch scratchOut _ partsRegular hs2 hn' hregular'
  simp only [↓reduceIte] at hp
  have sf := AspisR1S9SharedHighFrameV1.shared_high_success_frame
    partials selfCommon ap0 ap1 partsRegular partsShared hhigh
  have af := AspisR1S9ActiveFourFrameV1.inactive_active_preserves_point_parts
    f libra {start:=0#usize,«end»:=4#usize} partsShared partsInactive partsFinal inactive hpartsInactive hactive
  refine ⟨a0,a1,ha0,ha1,?_,?_,?_⟩
  · have he := (af 2#usize (by decide) (by decide) (by decide)).trans
      (sf 2#usize (by decide) (by decide) (by decide))
    exact (congrArg decodeNative he).trans hp.1
  · have he := (af 5#usize (by decide) (by decide) (by decide)).trans
      (sf 5#usize (by decide) (by decide) (by decide))
    exact (congrArg decodeNative he).trans hp.2.1
  · have he := (af 6#usize (by decide) (by decide) (by decide)).trans
      (sf 6#usize (by decide) (by decide) (by decide))
    exact (congrArg decodeNative he).trans hp.2.2

/-- SAME unshared actual trace final array has all five regular point/curve
part meanings. Its own later inactive0 and active4 writes preserve them;
actual alpha reads are exported, with no freely chosen alpha parameters. -/
theorem unshared_trace_final_regular_parts
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtor w))
    (hs2 : (fromCtor w).variant=transport.Variant.S2)
    (alpha : Slice NativeW) (f : Slice U8) (kappa out : NativeW)
    (partsFinal : Parts) (k : Array NativeW 7#usize)
    (halpha : ∀ (i : Usize) (a : NativeW),Slice.index_usize alpha i=.ok a → Can a)
    (htrace : AspisR1S9FinalPartsSourceTraceV1.UnsharedTrace
      (fromCtor w) alpha f kappa out partsFinal k) :
    ∃ a0 a1 : NativeW,
      Slice.index_usize alpha 0#usize=.ok a0 ∧ Slice.index_usize alpha 1#usize=.ok a1 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsFinal 1#usize (by decide) 0 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsFinal 2#usize (by decide) 1 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsFinal 3#usize (by decide) 2 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsFinal 5#usize (by decide) 3 ∧
      Means model (decodeNative a0) (decodeNative a1) f partsFinal 6#usize (by decide) 4 := by
  obtain ⟨hfold,hguard,hpair,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,
    low,inactive,partsInactive,useFactored,libra,
    hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩ := htrace
  have hregular' := hregular
  rw [hn64] at hregular'
  have hn' : (Slice.len f /32#usize : Result Usize)=.ok (64#usize) := by rw [←hn64];exact hn
  have hp := AspisR1S9RegularPhaseConstructorModelV1.actual_regular_phase_model_parts
    w model hm hc false alpha f a0 a1 (halpha 0#usize a0 ha0) (halpha 1#usize a1 ha1)
    ap0 ap1 hap0 hap1 scratch scratchOut _ partsRegular hs2 hn' hregular'
  simp only [Bool.false_eq_true,↓reduceIte] at hp
  have hactive' := hactive
  rw [AspisR1S9ActiveFourCanonicalV1.unshared_active_eq] at hactive'
  have frame := AspisR1S9ActiveFourFrameV1.inactive_active_preserves_point_parts
    f libra {start:=0#usize,«end»:=4#usize} partsRegular partsInactive partsFinal inactive hpartsInactive hactive'
  refine ⟨a0,a1,ha0,ha1,?_,?_,?_,?_,?_⟩
  · exact (congrArg decodeNative (frame 1#usize (by decide) (by decide) (by decide))).trans hp.1
  · exact (congrArg decodeNative (frame 2#usize (by decide) (by decide) (by decide))).trans hp.2.1
  · exact (congrArg decodeNative (frame 3#usize (by decide) (by decide) (by decide))).trans hp.2.2.1
  · exact (congrArg decodeNative (frame 5#usize (by decide) (by decide) (by decide))).trans hp.2.2.2.1
  · exact (congrArg decodeNative (frame 6#usize (by decide) (by decide) (by decide))).trans hp.2.2.2.2

#print axioms shared_trace_final_regular_parts
#print axioms unshared_trace_final_regular_parts
end AspisR1S9RegularTraceFinalModelV1
