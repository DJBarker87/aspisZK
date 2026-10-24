import S9ActualFinishDecodedStateV1
import S9PartialHighRawDomainV1
import S9NativeInputProductWitnessV1
import S9PartialDotOrderedTraceV1
import S9HighDotOrderedTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9PartialHighReturnedProductsV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9NativeInputProductWitnessV1
abbrev Dot := fast_pairing.EbyKDot
abbrev Common := Array NativeQ 16#usize
abbrev Partials := Array NativeW 4#usize
abbrev Coeffs := Array NativeQ 4#usize

/-- Full current source-body raw replacement, proved for each actual operand
below; this is an output fact, never an assumed dot-meaning contract. -/
def RawSourceEq (w : NativeW) : Prop :=
  ∀ dot scalar,
    AspisR1S9ActualRawEbyKBodyV1.pushWithRaw
      AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw dot w scalar =
      fast_pairing.EbyKDot.push dot w scalar

private theorem ordered_index_lt {n : Nat} (js : List Usize)
    (horder : js.map (fun j => j.val)=List.range' 0 n)
    (j : Usize) (hj : j ∈ js) : j.val < n := by
  have hm : j.val ∈ js.map (fun j => j.val) := List.mem_map.mpr ⟨j,hj,rfl⟩
  rw [horder] at hm
  have h := (List.mem_range'_1.mp hm).2
  simpa only [Nat.zero_add] using h

def partialReads (f : Slice U8) (common : Common) (s j : Usize) (p : NativePair) : Prop :=
  weights.field f (AspisR1S9PartialDotReaderDomainV1.index s j)=.ok p.1 ∧
    Array.index_usize common j=.ok p.2

def highReads (partials : Partials) (coeffs : Coeffs) (j : Usize) (p : NativePair) : Prop :=
  Array.index_usize partials j=.ok p.1 ∧ Array.index_usize coeffs j=.ok p.2

/-- SAME accepted partial call returns the ordered product sum of its actual
sixteen native read pairs. Its own initial zero state and SAME final finish
are supplied by the source trace; no separate finish/history/Can/model-value
premise is supplied to this theorem. -/
theorem actual_partial_returned_native_product_sum
    (f : Slice U8) (common : Common) (s : Usize) (hs : s.val < 4) (out : NativeW)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hrun : weights.partial_dot f common s=.ok (.Ok out)) :
    ∃ (js : List Usize) (ps : List NativePair) (final : Dot),
      fast_pairing.EbyKDot.finish final=.ok out ∧ ps.length=16 ∧
      js.map (fun j => j.val)=List.range' 0 16 ∧
      List.Forall₂ (partialReads f common s) js ps ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9ActualPairWideCanonicalV1.toCurrent out)=nativeProductSum ps ∧
      (∀ j ∈ js, ∀ p, partialReads f common s j p → RawSourceEq p.1) := by
  obtain ⟨js,xs,final,hfinish,hlen,hcorr,horder,hproduct⟩ :=
    AspisR1S9PartialDotOrderedTraceV1.actual_partial_source_product_sum
      f common s hs out hdiv hrun
  have hc : List.Forall₂ (fun j p => ∃ t, partialReads f common s j t ∧ p=sourcePair t)
      js xs := hcorr.imp (by
    intro j p hp
    obtain ⟨w,q,hw,hq,he⟩ := hp
    exact ⟨(w,q),⟨hw,hq⟩,he⟩)
  obtain ⟨ps,hreads,hmap⟩ := lift_source_inputs (partialReads f common s) js xs hc
  have hv := (AspisR1S9ActualFinishDecodedStateV1.actual_finish_success_decodes_state
    final out hfinish).trans hproduct
  rw [hmap] at hv
  refine ⟨js,ps,final,hfinish,hreads.length_eq.symm.trans hlen,horder,hreads,hv,?_⟩
  intro j hj p hp dot scalar
  exact AspisR1S9PartialHighRawDomainV1.partial_read_actual_raw_source_eq
    f s j hs (ordered_index_lt js horder j hj) hdiv p.1 hp.1 dot scalar

/-- SAME accepted shared-partials producer discharges all high input Can.
The SAME high call then returns the ordered product sum of its actual four
native read pairs and retains its actual final accumulator. -/
theorem actual_shared_high_returned_native_product_sum
    (f : Slice U8) (common : Common) (partials : Partials) (coeffs : Coeffs) (out : NativeW)
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (hrun : weights.high_dot partials coeffs=.ok (.Ok out)) :
    ∃ (js : List Usize) (ps : List NativePair) (final : Dot),
      fast_pairing.EbyKDot.finish final=.ok out ∧ ps.length=4 ∧
      js.map (fun j => j.val)=List.range' 0 4 ∧
      List.Forall₂ (highReads partials coeffs) js ps ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9ActualPairWideCanonicalV1.toCurrent out)=nativeProductSum ps ∧
      (∀ j ∈ js, ∀ p, highReads partials coeffs j p → RawSourceEq p.1) := by
  obtain ⟨js,xs,final,hfinish,hlen,hcorr,horder,hproduct⟩ :=
    AspisR1S9HighDotOrderedTraceV1.actual_shared_high_dot_source_product_sum
      f common partials coeffs out hproducer hrun
  have hc : List.Forall₂ (fun j p => ∃ t, highReads partials coeffs j t ∧ p=sourcePair t)
      js xs := hcorr.imp (by
    intro j p hp
    obtain ⟨w,q,hw,hq,he⟩ := hp
    exact ⟨(w,q),⟨hw,hq⟩,he⟩)
  obtain ⟨ps,hreads,hmap⟩ := lift_source_inputs (highReads partials coeffs) js xs hc
  have hv := (AspisR1S9ActualFinishDecodedStateV1.actual_finish_success_decodes_state
    final out hfinish).trans hproduct
  rw [hmap] at hv
  refine ⟨js,ps,final,hfinish,hreads.length_eq.symm.trans hlen,horder,hreads,hv,?_⟩
  intro j hj p hp dot scalar
  exact AspisR1S9PartialHighRawDomainV1.shared_high_read_actual_raw_source_eq
    f common partials hproducer j (ordered_index_lt js horder j hj) p.1 hp.1 dot scalar

#print axioms actual_partial_returned_native_product_sum
#print axioms actual_shared_high_returned_native_product_sum
end AspisR1S9PartialHighReturnedProductsV1
