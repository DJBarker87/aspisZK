import S9CurrentPairTensorModelV1
import S9ProcessKindScalarMeaningV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentPairTensorScalarModelV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9ActualPairScalarCallbackV1 (GoodArray)
open AspisR1S9FactorTableSemanticsV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def ScalarPrefix (self : weights.Weights) (kind : Usize) (ap0 ap1 : Powers) : Prop :=
    ∃ (row : Array (Array Q 4#usize) 5#usize) (f0 f1 : Array Q 4#usize)
      (scale0 scale1 scaleProduct : W),
      Array.index_usize self.factors (AspisR1S9ActualProcessKindTensorReachedV1.rowOfKind kind)=.ok row ∧
      Array.index_usize row 0#usize=.ok f0 ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.scalar_factor f0 ap0=.ok scale0 ∧
      Array.index_usize row 1#usize=.ok f1 ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.scalar_factor f1 ap1=.ok scale1 ∧
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul scale0 scale1=.ok scaleProduct ∧
      AspisR1S9ProcessKindScalarMeaningV1.ScalarMeaning f0 ap0 scale0 ∧ AspisR1S9ProcessKindScalarMeaningV1.ScalarMeaning f1 ap1 scale1

def ScalarKindCall (model : Table) (self : weights.Weights) (kind : Usize)
    (alpha : Slice W) (f : Slice U8) (folds n : Usize) (ap0 ap1 : Powers)
    (scratch scratchOut : Scratch) (parts partsOut : Parts) : Prop :=
  AspisR1S9CurrentPairTensorModelV1.ModelKindCall model self kind alpha f folds n ap0 ap1
    scratch scratchOut parts partsOut ∧ ScalarPrefix self kind ap0 ap1

def ScalarRegularTrace (model : Table) (self : weights.Weights) (shared : Bool)
    (alpha : Slice W) (f : Slice U8) (folds n : Usize) (ap0 ap1 : Powers)
    (scratch scratchOut : Scratch) (parts partsOut : Parts) : Prop :=
  if shared then
    ∃ (s1 s2 : Scratch) (p1 p2 : Parts),
      ScalarKindCall model self 2#usize alpha f folds n ap0 ap1 scratch s1 parts p1 ∧
      ScalarKindCall model self 5#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 ∧
      ScalarKindCall model self 6#usize alpha f folds n ap0 ap1 s2 scratchOut p2 partsOut
  else
    ∃ (s1 s2 s3 s4 : Scratch) (p1 p2 p3 p4 : Parts),
      ScalarKindCall model self 1#usize alpha f folds n ap0 ap1 scratch s1 parts p1 ∧
      ScalarKindCall model self 2#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 ∧
      ScalarKindCall model self 3#usize alpha f folds n ap0 ap1 s2 s3 p2 p3 ∧
      ScalarKindCall model self 5#usize alpha f folds n ap0 ap1 s3 s4 p3 p4 ∧
      ScalarKindCall model self 6#usize alpha f folds n ap0 ap1 s4 scratchOut p4 partsOut


/-- SAME model/scratch traces retain their tensor products and gain BOTH
actual scalar equations. Generic canonical guards are explicit here and are
discharged by the same-resume/Pair caller theorem. -/
theorem actual_trace_tensor_and_scalars
    (model : Table) (self : weights.Weights) (shared : Bool) (alpha : Slice W)
    (f : Slice U8) (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch)
    (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2)
    (hfactors : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical self)
    (hp0 : GoodArray ap0) (hp1 : GoodArray ap1)
    (htrace : AspisR1S9CurrentPairTensorModelV1.ModelRegularTrace model self shared
      alpha f 2#usize n ap0 ap1 scratch scratchOut parts partsOut) :
    ScalarRegularTrace model self shared alpha f 2#usize n ap0 ap1 scratch scratchOut parts partsOut := by
  have upgrade : ∀ kind s s' p p',
      AspisR1S9CurrentPairTensorModelV1.ModelKindCall model self kind alpha f 2#usize n ap0 ap1 s s' p p' →
      ScalarKindCall model self kind alpha f 2#usize n ap0 ap1 s s' p p' := by
    intro kind s s' p p' ht
    refine ⟨ht,?_⟩
    exact AspisR1S9ProcessKindScalarMeaningV1.process_kind_success_scalar_meanings
      self kind alpha f n ap0 ap1 s s' p p' (.Ok ()) hs2 hfactors hp0 hp1 ht.1
  cases shared with
  | true =>
    obtain ⟨s1,s2,p1,p2,h2,h5,h6⟩ := htrace
    exact ⟨s1,s2,p1,p2,upgrade _ _ _ _ _ h2,upgrade _ _ _ _ _ h5,upgrade _ _ _ _ _ h6⟩
  | false =>
    obtain ⟨s1,s2,s3,s4,p1,p2,p3,p4,h1,h2,h3,h5,h6⟩ := htrace
    exact ⟨s1,s2,s3,s4,p1,p2,p3,p4,upgrade _ _ _ _ _ h1,upgrade _ _ _ _ _ h2,
      upgrade _ _ _ _ _ h3,upgrade _ _ _ _ _ h5,upgrade _ _ _ _ _ h6⟩

#print axioms actual_trace_tensor_and_scalars
end AspisR1S9CurrentPairTensorScalarModelV1
