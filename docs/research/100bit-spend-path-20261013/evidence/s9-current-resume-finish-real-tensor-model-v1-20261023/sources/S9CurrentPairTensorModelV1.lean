import S9ActualPairTensorCallsV1
import S9CurrentReaderNativeProducersV1
import S9ActualConstructorNativeTensorV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentPairTensorModelV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9ActualRegularKindsTraceV1
open AspisR1S9ActualPairTensorCallsV1
open AspisR1S9FactorTableSemanticsV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev CW := AspisR1S9ActualWeightsNewBoxNewV3.Weights
abbrev nativeDecode := AspisR1S9ActualTensorArithmeticV1.decode
abbrev highProduct := AspisR1S9ActualTensorOuterSemanticsV1.highProduct
abbrev fromCtorWeights := AspisR1S9FinishActualConstructorSlotV1.fromCtorWeights

/-- Real kind call and its real tensor output, interpreted in ONE constructor model. -/
def ModelKindCall (model : Table) (self : weights.Weights) (kind : Usize)
    (alpha : Slice W) (f : Slice U8) (folds n : Usize) (ap0 ap1 : Powers)
    (scratch scratchOut : Scratch) (parts partsOut : Parts) : Prop :=
  KindCall self kind alpha f folds n ap0 ap1 scratch scratchOut parts partsOut ∧
    ∃ tensorOut : Slice Q, weights.Weights.tensor self (rowOfKind kind) folds
      (alloc.vec.Vec.deref_mut scratch).1=.ok tensorOut ∧
      AspisR1S9TensorIndexedMeaningV1.MeaningOn nativeDecode
        (highProduct (model (rowOfKind kind).val)) (fun i => i<64) tensorOut

def ModelRegularTrace (model : Table) (self : weights.Weights) (shared : Bool)
    (alpha : Slice W) (f : Slice U8) (folds n : Usize) (ap0 ap1 : Powers)
    (scratch scratchOut : Scratch) (parts partsOut : Parts) : Prop :=
  if shared then
    ∃ (s1 s2 : Scratch) (p1 p2 : Parts),
      ModelKindCall model self 2#usize alpha f folds n ap0 ap1 scratch s1 parts p1 ∧
      ModelKindCall model self 5#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 ∧
      ModelKindCall model self 6#usize alpha f folds n ap0 ap1 s2 scratchOut p2 partsOut
  else
    ∃ (s1 s2 s3 s4 : Scratch) (p1 p2 p3 p4 : Parts),
      ModelKindCall model self 1#usize alpha f folds n ap0 ap1 scratch s1 parts p1 ∧
      ModelKindCall model self 2#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 ∧
      ModelKindCall model self 3#usize alpha f folds n ap0 ap1 s2 s3 p2 p3 ∧
      ModelKindCall model self 5#usize alpha f folds n ap0 ap1 s3 s4 p3 p4 ∧
      ModelKindCall model self 6#usize alpha f folds n ap0 ap1 s4 scratchOut p4 partsOut

/-- A fixed complete constructor model interprets ALL actual regular tensor calls. -/
theorem actual_trace_same_model
    (w : CW) (model : Table) (self : weights.Weights)
    (hself : self=fromCtorWeights w) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical self)
    (shared : Bool) (alpha : Slice W) (f : Slice U8) (n : Usize) (ap0 ap1 : Powers)
    (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (ht : TensorRegularTrace self shared alpha f 2#usize n ap0 ap1 scratch scratchOut parts partsOut) :
    ModelRegularTrace model self shared alpha f 2#usize n ap0 ap1 scratch scratchOut parts partsOut := by
  have upgrade : ∀ (kind : Usize), (rowOfKind kind).val<5 →
      ∀ (s s' : Scratch) (p p' : Parts),
      TensorKindCall self kind alpha f 2#usize n ap0 ap1 s s' p p' →
      ModelKindCall model self kind alpha f 2#usize n ap0 ap1 s s' p p' := by
    intro kind hk s s' p p' hcall
    obtain ⟨hkind,tensorOut,htensor⟩ := hcall
    have hc' : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtorWeights w) := by
      rw [←hself]; exact hc
    have ht' : weights.Weights.tensor (fromCtorWeights w) (rowOfKind kind) 2#usize
        (alloc.vec.Vec.deref_mut s).1=.ok tensorOut := by
      rw [←hself]; exact htensor
    exact ⟨hkind,tensorOut,htensor,
      AspisR1S9ConstructorTableNativeTensorV1.native_tensor_success_table w model hm hc'
        (rowOfKind kind) hk (alloc.vec.Vec.deref_mut s).1 tensorOut ht'⟩
  have h1 : (rowOfKind 1#usize).val<5 := by rw [row_kind1]; change 0<5; decide
  have h2 : (rowOfKind 2#usize).val<5 := by rw [row_kind2]; change 1<5; decide
  have h3 : (rowOfKind 3#usize).val<5 := by rw [row_kind3]; change 2<5; decide
  have h5 : (rowOfKind 5#usize).val<5 := by rw [row_kind5]; change 3<5; decide
  have h6 : (rowOfKind 6#usize).val<5 := by rw [row_kind6]; change 4<5; decide
  cases shared with
  | true =>
    obtain ⟨s1,s2,p1,p2,t2,t5,t6⟩ := ht
    exact ⟨s1,s2,p1,p2,upgrade _ h2 _ _ _ _ t2,upgrade _ h5 _ _ _ _ t5,upgrade _ h6 _ _ _ _ t6⟩
  | false =>
    obtain ⟨s1,s2,s3,s4,p1,p2,p3,p4,t1,t2,t3,t5,t6⟩ := ht
    exact ⟨s1,s2,s3,s4,p1,p2,p3,p4,upgrade _ h1 _ _ _ _ t1,upgrade _ h2 _ _ _ _ t2,
      upgrade _ h3 _ _ _ _ t3,upgrade _ h5 _ _ _ _ t5,upgrade _ h6 _ _ _ _ t6⟩

#print axioms actual_trace_same_model
end AspisR1S9CurrentPairTensorModelV1
