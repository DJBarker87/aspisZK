import S9NativeFieldDivisionBoundV1
import S9ActualPairRegularPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairFieldReaderDomainV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9NativeFieldS5BoundedReaderV1
open AspisR1S9NativeFieldDivisionBoundV1
open AspisR1S9OwnedFromLimbsMapV1 (mapResult)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- The quotient and every bounded field/reader equality come from the SAME
accepted actual Pair call. Loop membership of a particular index remains a
separate obligation; no exact byte length is inferred from the quotient. -/
theorem actual_pair_success_bounded_field_reader
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hfold : Slice.len alpha = 2#usize)
    (h : weights.Weights.pair self alpha f kappa = .ok (.Ok out)) :
    ∃ n : Usize,
      (Slice.len f / 32#usize : Result Usize) = .ok n ∧
      ∀ i : Usize, i.val < n.val →
        (i.val + 1) * 32 ≤ f.val.length ∧
        mapResult toS5 (weights.field f i) =
          AspisR1S5PairCutTransparentReaderV1.readerBody
            AspisR1S5PairCutTransparentReaderV1.actualPairDecoder f i := by
  obtain ⟨n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
      hdiv,_⟩ :=
    AspisR1S9ActualPairRegularPrefixV1.actual_pair_success_regular_prefix
      self alpha f kappa out hfold h
  refine ⟨n,hdiv,?_⟩
  intro i hi
  exact ⟨quotient_index_fits f n i hdiv hi,
    quotient_index_maps_s5_reader f n i hdiv hi⟩

#print axioms actual_pair_success_bounded_field_reader
end AspisR1S9ActualPairFieldReaderDomainV1
