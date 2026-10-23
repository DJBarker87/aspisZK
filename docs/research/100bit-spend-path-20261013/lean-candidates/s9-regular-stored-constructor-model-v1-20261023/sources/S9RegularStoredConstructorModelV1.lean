import S9RegularKindConstructorModelV1
import S9ScalarConstructorModelV1
import S9NativeWideDecodedArithmeticV1
import S9ActualEbyKFinishCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open scoped BigOperators
namespace AspisR1S9RegularStoredConstructorModelV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9RegularKindExecutionV1
open AspisR1S9ConstructorTableNativeTensorV1
open AspisR1S9FactorTableSemanticsV1 (Table Meaning)
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
open AspisR1S9SharedSumObservationsV1 (fieldValue finIndex)
open AspisR1S9ScalarConstructorModelV1 (factorPolynomial)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical

private theorem decode_alias (x : W) :
    AspisR1S9NativeWideDecodedArithmeticV1.decode x=decodeNative x := rfl

private theorem decoded_mul_transport (p x y : W)
    (h : AspisR1S9NativeWideDecodedArithmeticV1.decode p=
      AspisR1S9NativeWideDecodedArithmeticV1.decode x*
        AspisR1S9NativeWideDecodedArithmeticV1.decode y) :
    decodeNative p=decodeNative x*decodeNative y := by
  exact (decode_alias p).symm.trans (h.trans
    (congrArg₂ (fun a b : AspisWideTower.WideExact => a*b)
      (decode_alias x) (decode_alias y)))

/-- SAME accepted regular driver stores its exact constructor-factor-weighted
source field sum. Source powers/canonical alpha inputs are supplied by the
same public caller producer; all scalar/dot/finish/multiply/write successes
are derived internally and retained in SAME Execution. -/
theorem actual_regular_stored_constructor_model
    (w : CW) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtorWeights w))
    (kind : Usize) (hk : (rowOfKind kind).val<5) (alpha : Slice W) (f : Slice U8)
    (a0 a1 : W) (ha0 : Can a0) (ha1 : Can a1) (ap0 ap1 : Powers)
    (hp0 : weights.powers 4#usize a0=.ok ap0)
    (hp1 : weights.powers 4#usize a1=.ok ap1)
    (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : (fromCtorWeights w).variant=transport.Variant.S2)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hcall : weights.process_kind (fromCtorWeights w) kind alpha f 2#usize 64#usize
      ap0 ap1 scratch parts=.ok (.Ok (),scratchOut,partsOut)) :
    ∃ e : Execution (fromCtorWeights w) kind f 64#usize ap0 ap1 scratch scratchOut parts partsOut,
      Can (Execution.storedValue e) ∧
      decodeNative (Execution.storedValue e)=
        factorPolynomial (decodeNative a0) (model (rowOfKind kind).val 0)*
        factorPolynomial (decodeNative a1) (model (rowOfKind kind).val 1)*
        (∑ i : Fin 64,fieldValue f (finIndex (by decide) i)*
          algebraMap AspisR1CurrentWide.Proof.ExactQM AspisWideTower.WideExact
            (highProduct (model (rowOfKind kind).val) i.val)) := by
  obtain ⟨e,hdot⟩ := AspisR1S9RegularKindConstructorModelV1.actual_regular_kind_constructor_model_sum
    w model hm hc kind hk alpha f ap0 ap1 scratch scratchOut parts partsOut hs2 hdiv hcall
  have h0 := AspisR1S9ScalarConstructorModelV1.actual_scalar_constructor_model
    w model hm hc (rowOfKind kind) 0#usize hk (by decide)
    (Execution.factorRow e) (Execution.f0 e) (Execution.factors e) (Execution.factor0 e)
    a0 ap0 (Execution.scale0 e) ha0 hp0 (Execution.scalar0 e)
  have h1 := AspisR1S9ScalarConstructorModelV1.actual_scalar_constructor_model
    w model hm hc (rowOfKind kind) 1#usize hk (by decide)
    (Execution.factorRow e) (Execution.f1 e) (Execution.factors e) (Execution.factor1 e)
    a1 ap1 (Execution.scale1 e) ha1 hp1 (Execution.scalar1 e)
  have hscale := AspisR1S9NativeWideDecodedArithmeticV1.actual_mul_success_decoded
    (Execution.scale0 e) (Execution.scale1 e) (Execution.scale e) h0.1 h1.1 (Execution.scaled e)
  have hdotCan := AspisR1S9ActualEbyKFinishCanonicalV1.actual_finish_success_canonical
    (Execution.finalDot e) (Execution.dotValue e) (Execution.finish e)
  have hv := AspisR1S9NativeWideDecodedArithmeticV1.actual_mul_success_decoded
    (Execution.scale e) (Execution.dotValue e) (Execution.storedValue e)
    hscale.1 hdotCan (Execution.product e)
  have hscaleNative := decoded_mul_transport
    (Execution.scale e) (Execution.scale0 e) (Execution.scale1 e) hscale.2
  have hvalueNative := decoded_mul_transport
    (Execution.storedValue e) (Execution.scale e) (Execution.dotValue e) hv.2
  refine ⟨e,hv.1,?_⟩
  exact hvalueNative.trans (congrArg₂ (fun x y : AspisWideTower.WideExact => x*y)
    (hscaleNative.trans (congrArg₂ (fun x y : AspisWideTower.WideExact => x*y) h0.2 h1.2)) hdot)

#print axioms actual_regular_stored_constructor_model
end AspisR1S9RegularStoredConstructorModelV1
