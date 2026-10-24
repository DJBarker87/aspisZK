import S9SharedSumObservationsV1
import S9SharedPartialsReadBindingsV1
import S9SharedContiguousTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9SharedDotContiguousSourceV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9PartialHighReturnedProductsV1
open AspisR1S9NativeDecodedScalarProductV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9SharedContiguousContractionV1
open AspisR1S9FactorArrayEntryV1

/-- Actual stored partial at this source index, not an assumed partial value. -/
theorem stored_partial_source_sum
    (f : Slice U8) (common : Common) (partials : Partials) (s : Usize) (hs : s.val<4)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hproducer : weights.shared_partials f common=.ok (.Ok partials)) :
    wideValue partials s=∑ j : Fin 16,
      fieldValue f (AspisR1S9PartialDotReaderDomainV1.index s (finIndex (by decide) j))*
        scalarValue common (finIndex (by decide) j) := by
  have hr := AspisR1S9SharedPartialsReadBindingsV1.actual_shared_partials_output_calls
    f common partials hproducer s hs
  have hv := partial_returned_source_sum f common s hs (atN partials s hs) hdiv hr
  simpa only [wideValue,index_atN partials s hs] using hv

theorem actual_shared_dot_double_sum
    (f : Slice U8) (common : Common) (partials : Partials) (coeffs : Coeffs) (out : NativeW)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (hrun : weights.high_dot partials coeffs=.ok (.Ok out)) :
    decodeNative out=∑ s : Fin 4,
      (∑ j : Fin 16,
        fieldValue f (AspisR1S9PartialDotReaderDomainV1.index
          (finIndex (by decide) s) (finIndex (by decide) j))*
          scalarValue common (finIndex (by decide) j))*
        scalarValue coeffs (finIndex (by decide) s) := by
  rw [high_returned_source_sum f common partials coeffs out hproducer hrun]
  apply Finset.sum_congr rfl
  intro s _
  rw [stored_partial_source_sum f common partials (finIndex (by decide) s)
    (by simpa only [finIndex_val] using s.isLt) hdiv hproducer]

theorem partial_index_contiguous (s : Fin 4) (j : Fin 16) :
    AspisR1S9PartialDotReaderDomainV1.index (finIndex (by decide) s) (finIndex (by decide) j)=
      finIndex (by decide : 64≤64) (sourceIndex s j) := by
  apply UScalar.eq_of_val_eq
  have hi := (AspisR1S9PartialDotReaderDomainV1.index_exact
    (finIndex (by decide) s) (finIndex (by decide) j)
    (by simpa only [finIndex_val] using s.isLt)
    (by simpa only [finIndex_val] using j.isLt)).1
  rw [hi]
  simp only [finIndex_val,sourceIndex_val]
  omega

/-- One actual shared-partials/high execution contracts EXACTLY the source
64-field contiguous stream with its actual low/high scalar arrays. All reads
and stored partial meanings are derived from those same source calls. -/
theorem actual_shared_dot_flat64
    (f : Slice U8) (common : Common) (partials : Partials) (coeffs : Coeffs) (out : NativeW)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (hrun : weights.high_dot partials coeffs=.ok (.Ok out)) :
    decodeNative out=∑ i : Fin 64,
      fieldValue f (finIndex (by decide) i)*
        tensorWeight
          (fun j : Fin 16 => scalarValue common (finIndex (by decide) j))
          (fun s : Fin 4 => scalarValue coeffs (finIndex (by decide) s)) i := by
  exact AspisR1S9SharedContiguousTransportV1.transport_source_sum
    (fun s : Fin 4 => fun j : Fin 16 => fieldValue f
      (AspisR1S9PartialDotReaderDomainV1.index (finIndex (by decide) s) (finIndex (by decide) j)))
    (fun i : Fin 64 => fieldValue f (finIndex (by decide) i))
    (fun j : Fin 16 => scalarValue common (finIndex (by decide) j))
    (fun s : Fin 4 => scalarValue coeffs (finIndex (by decide) s))
    (decodeNative out)
    (fun s j => congrArg (fieldValue f) (partial_index_contiguous s j))
    (actual_shared_dot_double_sum f common partials coeffs out hdiv hproducer hrun)

#print axioms stored_partial_source_sum
#print axioms actual_shared_dot_double_sum
#print axioms partial_index_contiguous
#print axioms actual_shared_dot_flat64
end AspisR1S9SharedDotContiguousSourceV1
