import S9SharedDotContiguousSourceV1
import S9SharedScalarModelValuesV1
import S9TensorModelTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9SharedDotConstructorModelV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9SharedDotContiguousSourceV1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
abbrev E := AspisWideTower.WideExact
abbrev Partials := Array NativeW 4#usize
abbrev Coeffs := Array NativeQ 4#usize

/-- SAME source constructor/common producer, actual row/cell reads and
actual shared partial/high calls determine the exact constructor-table
weighted64-field sum. No desired operand/factor/dot-value premises remain;
table meaning/canonical receiver are supplied by the same constructor bridge.
The two shared rows use the same row0 low factors and own row-specific high. -/
theorem actual_shared_dot_constructor_cross_product
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtor w))
    (selfOut : weights.Weights) (initial common : Common)
    (hloop : weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
      (fromCtor w) initial=.ok (selfOut,common))
    (k : Usize) (hk : k.val<5) (row : Row) (coeffs : Coeffs)
    (hr : Array.index_usize (fromCtor w).factors k=.ok row)
    (hcell : Array.index_usize row 4#usize=.ok coeffs)
    (f : Slice U8) (partials : Partials) (out : NativeW)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (hrun : weights.high_dot partials coeffs=.ok (.Ok out)) :
    decodeNative out=∑ i : Fin 64,fieldValue f (finIndex (by decide) i)*
      embedQ (model 0 2 (i.val%4)*model 0 3 ((i.val/4)%4)*model k.val 4 ((i.val/16)%4)) := by
  have hlow := (common_scalar_values_model w model hm hc selfOut initial common hloop).2
  have hhigh := factor_scalar_values_model w model hm k 4#usize hk (by decide) row coeffs hr hcell
  have hvalue := actual_shared_dot_flat64 f common partials coeffs out hdiv hproducer hrun
  exact AspisR1S9TensorModelTransportV1.transport_model_sum
    (algebraMap ExactQM E) (model 0 2) (model 0 3) (model k.val 4)
    (fun i : Fin 64 => fieldValue f (finIndex (by decide) i))
    (fun j : Fin 16 => scalarValue common (finIndex (by decide) j))
    (fun s : Fin 4 => scalarValue coeffs (finIndex (by decide) s))
    (decodeNative out) hlow hhigh hvalue

#print axioms actual_shared_dot_constructor_cross_product
end AspisR1S9SharedDotConstructorModelV1
