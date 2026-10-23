import S9RegularStoredConstructorModelV1
import S9RegularRowIndicesV1
import S9ActualRegularKindsTraceV1
import S9FactorArrayEntryV1
import S9SharedHighConstructorModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open scoped BigOperators
namespace AspisR1S9RegularPhaseConstructorModelV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9RegularKindExecutionV1
open AspisR1S9ActualRegularKindsTraceV1
open AspisR1S9FactorArrayEntryV1
open AspisR1S9ConstructorTableNativeTensorV1
open AspisR1S9FactorTableSemanticsV1 (Table Meaning)
open AspisR1S9RegularRowIndicesV1
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev E := AspisWideTower.WideExact
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical

def Means (model : Table) (a0 a1 : E) (f : Slice U8) (parts : Parts)
    (j : Usize) (hj : j.val<7) (row : Nat) : Prop :=
  decodeNative (atN parts j hj)=rowValue model a0 a1 f row

private def fieldVectorWithProof (h : 64≤64) (f : Slice U8) : Fin 64 → E :=
  fun i => AspisR1S9SharedSumObservationsV1.fieldValue f
    (AspisR1S9SharedSumObservationsV1.finIndex h i)

private theorem fieldVector_proof_irrel (h1 h2 : 64≤64) :
    fieldVectorWithProof h1=fieldVectorWithProof h2 := by
  have he : h1=h2 := Subsingleton.elim _ _
  cases he
  rfl

/-- Later distinct-index writes preserve the exact earlier source value. -/
theorem kind_success_other_index_frame
    (self : weights.Weights) (kind j : Usize) (alpha : Slice W) (f : Slice U8) (n : Usize)
    (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2) (hk : kind.val<7) (hj : j.val<7)
    (hne : j.val≠kind.val)
    (hcall : weights.process_kind self kind alpha f 2#usize n ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) : atN partsOut j hj=atN parts j hj := by
  obtain ⟨e⟩ := process_kind_success_execution self kind alpha f n ap0 ap1 scratch scratchOut parts partsOut hs2 hcall
  have he := accepted_update_eq_set parts kind hk (Execution.storedValue e) partsOut (Execution.write e)
  rw [he,atN_set parts kind j (Execution.storedValue e) hk hj,if_neg hne]

theorem kind_success_stored_model
    (w : CW) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtorWeights w))
    (kind : Usize) (hk : kind.val<7) (hr : (rowOfKind kind).val<5)
    (alpha : Slice W) (f : Slice U8) (a0 a1 : W) (ha0 : Can a0) (ha1 : Can a1)
    (ap0 ap1 : Powers) (hp0 : weights.powers 4#usize a0=.ok ap0)
    (hp1 : weights.powers 4#usize a1=.ok ap1)
    (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : (fromCtorWeights w).variant=transport.Variant.S2)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hcall : weights.process_kind (fromCtorWeights w) kind alpha f 2#usize 64#usize ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) :
    Means model (decodeNative a0) (decodeNative a1) f partsOut kind hk (rowOfKind kind).val := by
  obtain ⟨e,hcan,hval⟩ := AspisR1S9RegularStoredConstructorModelV1.actual_regular_stored_constructor_model
    w model hm hc kind hr alpha f a0 a1 ha0 ha1 ap0 ap1 hp0 hp1 scratch scratchOut parts partsOut hs2 hdiv hcall
  have he := accepted_update_eq_set parts kind hk (Execution.storedValue e) partsOut (Execution.write e)
  have hset : atN (parts.set kind (Execution.storedValue e)) kind hk=Execution.storedValue e := by
    rw [atN_set parts kind kind (Execution.storedValue e) hk hk,if_pos rfl]
  have hread : atN partsOut kind hk=Execution.storedValue e :=
    (congrArg (fun a : Parts => atN a kind hk) he).trans hset
  have hind := congrFun (fieldVector_proof_irrel (by decide)
    AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1) f
  have hsum := congrArg (fun g : Fin 64 → E =>
    ∑ i : Fin 64,g i*algebraMap AspisR1CurrentWide.Proof.ExactQM E
      (highProduct (model (rowOfKind kind).val) i.val)) hind
  have hscaled := congrArg (fun z : E =>
    AspisR1S9ScalarConstructorModelV1.factorPolynomial (decodeNative a0) (model (rowOfKind kind).val 0)*
    AspisR1S9ScalarConstructorModelV1.factorPolynomial (decodeNative a1) (model (rowOfKind kind).val 1)*z) hsum
  have hvCanonical := hval.trans hscaled
  have hvRow : decodeNative (Execution.storedValue e)=
      rowValue model (decodeNative a0) (decodeNative a1) f (rowOfKind kind).val := by
    unfold rowValue AspisR1S9SharedScalarModelValuesV1.embedQ
    simpa only [fieldVectorWithProof,AspisR1S9SharedScalarModelValuesV1.E,
      AspisR1S9SharedScalarModelValuesV1.ExactQM,AspisR1S9SharedSumObservationsV1.E] using hvCanonical
  exact (congrArg decodeNative hread).trans hvRow

#print axioms kind_success_other_index_frame
#print axioms kind_success_stored_model
end AspisR1S9RegularPhaseConstructorModelV1
