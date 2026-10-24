import S9PartialHighReturnedProductsV1
import S9NativeProductFinSumV1
import S9OrderedNativeReadConsistencyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open scoped BigOperators
namespace AspisR1S9PartialHighReturnedFinProductsV1
open AspisR1S9PartialHighReturnedProductsV1
open AspisR1S9NativeInputProductWitnessV1
open AspisR1S9NativeDecodedScalarProductV1
open AspisR1S9NativeProductFinSumV1
open AspisR1S9ActualEbyKBackendTransportV1

/-- Ordinary decoded-Wide multiplication over EXACT Fin16 order. The actual
read pairs, their derived length, source order and SAME final finish are
retained; no desired operand values or mathematical finish are premises. -/
theorem actual_partial_returned_fin16_product_sum
    (f : Slice U8) (common : Common) (s : Usize) (hs : s.val < 4) (out : NativeW)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hrun : weights.partial_dot f common s=.ok (.Ok out)) :
    ∃ (js : List Usize) (ps : List NativePair) (final : Dot) (hlen : ps.length=16),
      fast_pairing.EbyKDot.finish final=.ok out ∧
      js.map (fun j => j.val)=List.range' 0 16 ∧
      List.Forall₂ (partialReads f common s) js ps ∧
      (∀ i : Fin 16, ∃ j : Usize, j.val=i.val ∧
        partialReads f common s j (ps.get (Fin.cast hlen.symm i))) ∧
      decodeNative out = (∑ i : Fin 16,
        decodeNative (ps.get (Fin.cast hlen.symm i)).1 *
          scalarEmbed (ps.get (Fin.cast hlen.symm i)).2) ∧
      (∀ j ∈ js, ∀ p, partialReads f common s j p → RawSourceEq p.1) := by
  obtain ⟨js,ps,final,hfinish,hlen,horder,hreads,hvalue,hraw⟩ :=
    actual_partial_returned_native_product_sum f common s hs out hdiv hrun
  have hsum := nativeProductSum_eq_fin_sum_cast ps 16 hlen
  have hpositions := fun i : Fin 16 =>
    AspisR1S9OrderedNativeReadConsistencyV1.ordered_forall2_get
      (partialReads f common s) js ps 16 hlen hreads horder i
  exact ⟨js,ps,final,hlen,hfinish,horder,hreads,hpositions,hvalue.trans hsum,hraw⟩

/-- Ordinary decoded-Wide multiplication over EXACT Fin4 order, from the
SAME actual shared-partials producer/high call and exact native input reads. -/
theorem actual_shared_high_returned_fin4_product_sum
    (f : Slice U8) (common : Common) (partials : Partials) (coeffs : Coeffs) (out : NativeW)
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (hrun : weights.high_dot partials coeffs=.ok (.Ok out)) :
    ∃ (js : List Usize) (ps : List NativePair) (final : Dot) (hlen : ps.length=4),
      fast_pairing.EbyKDot.finish final=.ok out ∧
      js.map (fun j => j.val)=List.range' 0 4 ∧
      List.Forall₂ (highReads partials coeffs) js ps ∧
      (∀ i : Fin 4, ∃ j : Usize, j.val=i.val ∧
        highReads partials coeffs j (ps.get (Fin.cast hlen.symm i))) ∧
      decodeNative out = (∑ i : Fin 4,
        decodeNative (ps.get (Fin.cast hlen.symm i)).1 *
          scalarEmbed (ps.get (Fin.cast hlen.symm i)).2) ∧
      (∀ j ∈ js, ∀ p, highReads partials coeffs j p → RawSourceEq p.1) := by
  obtain ⟨js,ps,final,hfinish,hlen,horder,hreads,hvalue,hraw⟩ :=
    actual_shared_high_returned_native_product_sum f common partials coeffs out hproducer hrun
  have hsum := nativeProductSum_eq_fin_sum_cast ps 4 hlen
  have hpositions := fun i : Fin 4 =>
    AspisR1S9OrderedNativeReadConsistencyV1.ordered_forall2_get
      (highReads partials coeffs) js ps 4 hlen hreads horder i
  exact ⟨js,ps,final,hlen,hfinish,horder,hreads,hpositions,hvalue.trans hsum,hraw⟩

#print axioms actual_partial_returned_fin16_product_sum
#print axioms actual_shared_high_returned_fin4_product_sum
end AspisR1S9PartialHighReturnedFinProductsV1
