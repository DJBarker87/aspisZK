import S9SharedDotConstructorModelV1
import S9ActualSharedGuardTableV1
import S9SharedDotContiguousSourceV1
import S9SharedScalarModelValuesV1
import S9TensorModelTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9SharedDotGuardModelV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9SharedDotContiguousSourceV1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
abbrev E := AspisWideTower.WideExact
abbrev Partials := Array NativeW 4#usize
abbrev Coeffs := Array NativeQ 4#usize

/-- The actual shared guard identifies the row-two high product on the SAME receiver. --/
theorem actual_shared_row_two_dot_model
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtor w))
    (selfOut : weights.Weights) (initial common : Common)
    (hloop : weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
      (fromCtor w) initial=.ok (selfOut,common))
    (folds : Usize)
    (hguard : weights.shared_two_point_guard (fromCtor w) folds=.ok true)
    (row : Row) (coeffs : Coeffs)
    (hr : Array.index_usize (fromCtor w).factors 2#usize=.ok row)
    (hcell : Array.index_usize row 4#usize=.ok coeffs)
    (f : Slice U8) (partials : Partials) (out : NativeW)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (hrun : weights.high_dot partials coeffs=.ok (.Ok out)) :
    decodeNative out=∑ i : Fin 64,fieldValue f (finIndex (by decide) i)*
      embedQ (AspisR1S9ConstructorTableNativeTensorV1.highProduct (model 2) i.val) := by
  have hv := AspisR1S9SharedDotConstructorModelV1.actual_shared_dot_constructor_cross_product
    w model hm hc selfOut initial common hloop 2#usize (by decide) row coeffs hr hcell
    f partials out hdiv hproducer hrun
  have hg := (AspisR1S9ActualSharedGuardTableV1.guard_true_table_high_products
    w model hm folds hguard).2.2
  calc
    _ = _ := hv
    _ = _ := Finset.sum_congr rfl (fun i _ => by rw [hg i.val])

#print axioms actual_shared_row_two_dot_model
end AspisR1S9SharedDotGuardModelV1
