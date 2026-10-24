import S9NativePushNewProductV1
import S9NativePushTraceOrderV1
import S9ActualFinishDecodedStateV1
import S9NativeInputProductWitnessV1
import S9NativeProductFinSumV1
import S9OrderedNativeReadConsistencyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open scoped BigOperators
namespace AspisR1S9RegularReturnedFinProductsV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9NativeInputProductWitnessV1
open AspisR1S9NativeDecodedScalarProductV1
open AspisR1S9NativeProductFinSumV1
abbrev Dot := fast_pairing.EbyKDot

def actualReads (f : Slice U8) (scratch : Slice NativeQ) (j : Usize) (p : NativePair) : Prop :=
  weights.field f j=.ok p.1 ∧ Slice.index_usize scratch j=.ok p.2

/-- The exact actual inlined regular driver's new/push/finish chain returns
its own ordered operand sum. The source count is retained symbolically;
no scratch meaning, input canonicality, accumulator history or model finish
is assumed. Caller specialization derives 64 from its actual byte span. -/
theorem actual_new_push_finish_returned_fin_product_sum
    (f : Slice U8) (scratch : Slice NativeQ) (n : Usize)
    (initial final : Dot) (out : NativeW)
    (hnew : fast_pairing.EbyKDot.new=.ok initial)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok n)
    (hpush : weights.push_byte_products initial f scratch n=.ok (.Ok (),final))
    (hfinish : fast_pairing.EbyKDot.finish final=.ok out) :
    ∃ (js : List Usize) (ps : List NativePair) (hlen : ps.length=n.val),
      js.map (fun j => j.val)=List.range' 0 n.val ∧
      List.Forall₂ (actualReads f scratch) js ps ∧
      (∀ i : Fin n.val, ∃ j : Usize, j.val=i.val ∧
        actualReads f scratch j (ps.get (Fin.cast hlen.symm i))) ∧
      decodeNative out=(∑ i : Fin n.val,
        decodeNative (ps.get (Fin.cast hlen.symm i)).1 *
          scalarEmbed (ps.get (Fin.cast hlen.symm i)).2) := by
  obtain ⟨js,xs,htrace,hlen,hcorr,hproduct⟩ :=
    AspisR1S9NativePushNewProductV1.actual_new_push_products_decoded_sum
      f scratch n initial final hnew hdiv hpush
  have hc : List.Forall₂ (fun j p => ∃ t, actualReads f scratch j t ∧ p=sourcePair t)
      js xs := hcorr.imp (by
    intro j p hp
    obtain ⟨w,q,hw,hq,he⟩ := hp
    exact ⟨(w,q),⟨hw,hq⟩,he⟩)
  obtain ⟨ps,hreads,hmap⟩ := lift_source_inputs (actualReads f scratch) js xs hc
  have hv := (AspisR1S9ActualFinishDecodedStateV1.actual_finish_success_decodes_state
    final out hfinish).trans hproduct
  rw [hmap] at hv
  have hpLen : ps.length=n.val := hreads.length_eq.symm.trans hlen
  have horder := AspisR1S9NativePushTraceOrderV1.trace_indices_order
    f scratch n {start:=0#usize,«end»:=n} initial final js htrace
  have horder' : js.map (fun j => j.val)=List.range' 0 n.val := by
    change js.map (fun j => j.val)=List.range' 0 js.length at horder
    simpa only [hlen] using horder
  have hpositions := fun i : Fin n.val =>
    AspisR1S9OrderedNativeReadConsistencyV1.ordered_forall2_get
      (actualReads f scratch) js ps n.val hpLen hreads horder' i
  exact ⟨js,ps,hpLen,horder',hreads,hpositions,
    hv.trans (nativeProductSum_eq_fin_sum_cast ps n.val hpLen)⟩

#print axioms actual_new_push_finish_returned_fin_product_sum
end AspisR1S9RegularReturnedFinProductsV1
