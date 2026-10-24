import S9SharedHighConstructorModelV1
import S9FinalPartsSourceTraceV1
import S9ActiveFourFrameV1
import S9RegularPartsCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SharedTracePointPartsV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
open AspisR1S9FactorArrayEntryV1
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev Parts := AspisR1S9ActualProcessKindTensorReachedV1.Parts
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- SAME final parts from the actual shared source trace, not an existential
replacement vector, have their own constructor-model expressions in slots1/3.
Later inactive/private writes preserve these exact cells. -/
theorem shared_trace_final_point_parts
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtor w))
    (hs2 : (fromCtor w).variant=transport.Variant.S2)
    (alpha : Slice NativeW) (f : Slice U8) (kappa out : NativeW)
    (partsFinal : Parts) (k : Array NativeW 7#usize)
    (halpha : ∀ (i : Usize) (a : NativeW),Slice.index_usize alpha i=.ok a → Can a)
    (htrace : AspisR1S9FinalPartsSourceTraceV1.SharedTrace
      (fromCtor w) alpha f kappa out partsFinal k) :
    ∃ a0 a1 : NativeW,
      Slice.index_usize alpha 0#usize=.ok a0 ∧
      Slice.index_usize alpha 1#usize=.ok a1 ∧
      decodeNative (atN partsFinal 1#usize (by decide))=
        rowValue model (decodeNative a0) (decodeNative a1) f 0 ∧
      decodeNative (atN partsFinal 3#usize (by decide))=
        rowValue model (decodeNative a0) (decodeNative a1) f 2 := by
  obtain ⟨hfold,hguard,hpair,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,partsShared,
    selfCommon,common,partials,low,inactive,partsInactive,useFactored,libra,
    hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hcommon,hpartials,hhigh,
    hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩ := htrace
  have ha0c := halpha 0#usize a0 ha0
  have ha1c := halpha 1#usize a1 ha1
  have hcap0 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical a0 ap0 ha0c hap0
  have hcap1 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical a1 ap1 ha1c hap1
  have hpg := AspisR1S9RegularPartsCanonicalV1.regular_from_zero_success_good
    (fromCtor w) true alpha f n ap0 ap1 scratch scratchOut partsRegular hs2 hcap0 hcap1 hregular
  have hcommonSelf := (AspisR1S9SharedScalarModelValuesV1.common_scalar_values_model
    w model hm hc selfCommon _ common hcommon).1
  have hhigh' := hhigh
  rw [hcommonSelf] at hhigh'
  have hn' : (Slice.len f /32#usize : Result Usize)=.ok (64#usize) := by rw [←hn64]; exact hn
  obtain ⟨p0,p2,cp0,cp2,hout,hv0,hv2⟩ :=
    AspisR1S9SharedHighConstructorModelV1.actual_shared_high_model_writes
      w model hm hc selfCommon _ common hcommon hguard a0 a1 ap0 ap1 ha0c ha1c hap0 hap1
      f partials partsRegular partsShared hn' hpartials hpg hhigh'
  have frame := AspisR1S9ActiveFourFrameV1.inactive_active_preserves_point_parts
    f libra {start:=0#usize,«end»:=4#usize} partsShared partsInactive partsFinal inactive hpartsInactive hactive
  have e1 : atN partsShared 1#usize (by decide)=p0 := by
    rw [hout,atN_set (partsRegular.set 1#usize p0) 3#usize 1#usize p2 (by decide) (by decide),
      atN_set partsRegular 1#usize 1#usize p0 (by decide) (by decide)]; rfl
  have e3 : atN partsShared 3#usize (by decide)=p2 := by
    rw [hout,atN_set (partsRegular.set 1#usize p0) 3#usize 3#usize p2 (by decide) (by decide)]; rfl
  refine ⟨a0,a1,ha0,ha1,?_,?_⟩
  · rw [frame 1#usize (by decide) (by decide) (by decide),e1]; exact hv0
  · rw [frame 3#usize (by decide) (by decide) (by decide),e3]; exact hv2

#print axioms shared_trace_final_point_parts
end AspisR1S9SharedTracePointPartsV1
