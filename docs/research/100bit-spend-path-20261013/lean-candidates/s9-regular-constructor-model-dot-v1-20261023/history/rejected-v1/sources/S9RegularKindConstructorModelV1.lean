import S9RegularKindReturnedFinProductsV1
import S9RegularTensorModelWeightV1
import S9SharedSumObservationsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open scoped BigOperators
namespace AspisR1S9RegularKindConstructorModelV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9RegularKindExecutionV1
open AspisR1S9ConstructorTableNativeTensorV1
open AspisR1S9FactorTableSemanticsV1 (Table Meaning)
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
open AspisR1S9SharedSumObservationsV1 (fieldValue finIndex finIndex_val)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- SAME accepted regular process_kind returns the constructor model's exact
high-factor weighted64-field sum, with the complete SAME source Execution
retained. fieldValue observes the actual source f; no free coefficient vector,
callee-success, desired tensor values or standalone tensor_dot are premises.
Constructor table/Can and actual row bound are supplied by the source caller. -/
theorem actual_regular_kind_constructor_model_sum
    (w : CW) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtorWeights w))
    (kind : Usize) (hk : (rowOfKind kind).val<5) (alpha : Slice W) (f : Slice U8)
    (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : (fromCtorWeights w).variant=transport.Variant.S2)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hcall : weights.process_kind (fromCtorWeights w) kind alpha f 2#usize 64#usize
      ap0 ap1 scratch parts=.ok (.Ok (),scratchOut,partsOut)) :
    ∃ e : Execution (fromCtorWeights w) kind f 64#usize ap0 ap1 scratch scratchOut parts partsOut,
      decodeNative (Execution.dotValue e)=∑ i : Fin 64,
        fieldValue f (finIndex (by decide) i)*
          algebraMap AspisR1CurrentWide.Proof.ExactQM AspisWideTower.WideExact
            (highProduct (model (rowOfKind kind).val) i.val) := by
  obtain ⟨e,js,ps,hlen,horder,hreads,hpositions,hvalue,hraw⟩ :=
    AspisR1S9RegularKindReturnedFinProductsV1.actual_process_kind_returned_fin_products
      (fromCtorWeights w) kind alpha f 64#usize ap0 ap1 scratch scratchOut parts partsOut hs2 hdiv hcall
  refine ⟨e,hvalue.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨j,hj,hread⟩ := hpositions i
  have hi : j.val<64 := by rw [hj];exact i.isLt
  have hscalar := AspisR1S9RegularTensorModelWeightV1.actual_regular_tensor_read_model_weight
    w model hm hc kind hk f ap0 ap1 scratch scratchOut parts partsOut e j hi
      (ps.get (Fin.cast hlen.symm i)).2 hread.2
  rw [hj] at hscalar
  have he : j=finIndex (by decide : 64≤64) i :=
    UScalar.eq_of_val_eq (hj.trans (finIndex_val (by decide) i).symm)
  have hfield : fieldValue f (finIndex (by decide) i)=
      decodeNative (ps.get (Fin.cast hlen.symm i)).1 := by
    unfold fieldValue
    rw [←he,hread.1]
  exact congrArg₂ (fun x y : AspisWideTower.WideExact => x*y) hfield.symm hscalar

#print axioms actual_regular_kind_constructor_model_sum
end AspisR1S9RegularKindConstructorModelV1
