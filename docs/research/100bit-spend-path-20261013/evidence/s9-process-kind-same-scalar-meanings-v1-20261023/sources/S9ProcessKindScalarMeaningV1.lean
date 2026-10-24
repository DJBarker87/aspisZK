import S9ProcessKindScalarSourceV1
import S9ActualScalarNativeReadsV1
import S9ConstructorNativeReceiverCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ProcessKindScalarMeaningV1
open AspisR1S9ActualPairScalarCallbackV1
abbrev Weights := AspisR1S9ProductionPairCutV1.weights.Weights
abbrev Scratch := AspisR1S9ActualProcessKindTensorReachedV1.Scratch
abbrev Powers := AspisR1S9ActualProcessKindTensorReachedV1.Powers
abbrev Parts := AspisR1S9ActualProcessKindTensorReachedV1.Parts
abbrev Outcome := AspisR1S9ActualProcessKindTensorReachedV1.Outcome
abbrev rowOfKind := AspisR1S9ActualProcessKindTensorReachedV1.rowOfKind
abbrev E := AspisWideTower.WideExact
abbrev nativeTerm := AspisR1S9ActualScalarNativeReadsV1.nativeTerm
abbrev decodeNative := AspisR1S9ActualScalarFourTermMeaningV1.decodeNative
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def ScalarMeaning (f : Array Q 4#usize) (p : Array W 4#usize) (out : W) : Prop :=
    Canonical out ∧ ∃ (p0 p1 p2 p3 : W) (q0 q1 q2 q3 : Q),
      Array.index_usize p 0#usize=.ok p0 ∧ Array.index_usize f 0#usize=.ok q0 ∧
      Array.index_usize p 3#usize=.ok p1 ∧ Array.index_usize f 1#usize=.ok q1 ∧
      Array.index_usize p 2#usize=.ok p2 ∧ Array.index_usize f 2#usize=.ok q2 ∧
      Array.index_usize p 1#usize=.ok p3 ∧ Array.index_usize f 3#usize=.ok q3 ∧
      decodeNative out = (((((0 : E)+nativeTerm p0 q0)+nativeTerm p1 q1)+
        nativeTerm p2 q2)+nativeTerm p3 q3)*
        AspisR1CurrentWide.Proof.wideScalarEmbedding
          AspisR1S9ProductionPairCutV1.weights.QUARTER

/-- Both real scalar calls of this SAME process_kind have their native
PERM/quarter equations. Factor-vector canonicality is DERIVED from the same
receiver's 3D canonical read contract and the source d0/d1 reads; no child
scalar-success or independent fCanonical premise remains. -/
theorem process_kind_success_scalar_meanings
    (self : Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8)
    (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch)
    (parts partsOut : Parts) (result : Outcome)
    (hs2 : self.variant=AspisR1S9ProductionPairCutV1.transport.Variant.S2)
    (hfactors : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical self)
    (hp0 : GoodArray ap0) (hp1 : GoodArray ap1)
    (hcall : AspisR1S9ProductionPairCutV1.weights.process_kind self kind alpha f 2#usize n
      ap0 ap1 scratch parts=.ok (result,scratchOut,partsOut)) :
    ∃ (row : Array (Array Q 4#usize) 5#usize) (f0 f1 : Array Q 4#usize)
      (scale0 scale1 scaleProduct : W),
      Array.index_usize self.factors (rowOfKind kind)=.ok row ∧
      Array.index_usize row 0#usize=.ok f0 ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.scalar_factor f0 ap0=.ok scale0 ∧
      Array.index_usize row 1#usize=.ok f1 ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.scalar_factor f1 ap1=.ok scale1 ∧
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul scale0 scale1=.ok scaleProduct ∧
      ScalarMeaning f0 ap0 scale0 ∧ ScalarMeaning f1 ap1 scale1 := by
  obtain ⟨row,f0,f1,scale0,scale1,scaleProduct,hr,hf0,hs0,hf1,hs1,hm⟩ :=
    AspisR1S9ProcessKindScalarSourceV1.process_kind_success_reaches_scalars
      self kind alpha f n ap0 ap1 scratch scratchOut parts partsOut result hs2 hcall
  have hq0 : AspisR1S9ActualScalarFourTermMeaningV1.GoodQArray f0 := by
    intro i q hq
    exact hfactors (rowOfKind kind) 0#usize row f0 i q hr hf0 hq
  have hq1 : AspisR1S9ActualScalarFourTermMeaningV1.GoodQArray f1 := by
    intro i q hq
    exact hfactors (rowOfKind kind) 1#usize row f1 i q hr hf1 hq
  have hmeaning0 : ScalarMeaning f0 ap0 scale0 :=
    AspisR1S9ActualScalarNativeReadsV1.actual_scalar_success_native_reads_quarter f0 ap0 scale0 hp0 hq0 hs0
  have hmeaning1 : ScalarMeaning f1 ap1 scale1 :=
    AspisR1S9ActualScalarNativeReadsV1.actual_scalar_success_native_reads_quarter f1 ap1 scale1 hp1 hq1 hs1
  exact ⟨row,f0,f1,scale0,scale1,scaleProduct,hr,hf0,hs0,hf1,hs1,hm,hmeaning0,hmeaning1⟩

#print axioms process_kind_success_scalar_meanings
end AspisR1S9ProcessKindScalarMeaningV1
