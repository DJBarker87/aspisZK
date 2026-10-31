import NEB_ArrayRefs
import NEB_PureFrame
import NBG_Embedding
set_option autoImplicit false
noncomputable section
namespace NEB_WideRepresentation
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_ArrayRefs
abbrev EQ := AspisS1M31Embedding.aspis_core.field.QM31
abbrev EE := AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact

def into (x : NQ) : EQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def normalized (x : NQ) : NQ :=
  ⟨⟨AspisS1M31Embedding.Total.reduce x.c0.a,AspisS1M31Embedding.Total.reduce x.c0.b⟩,
   ⟨AspisS1M31Embedding.Total.reduce x.c1.a,AspisS1M31Embedding.Total.reduce x.c1.b⟩⟩
def embedded (x : NQ) : EE :=
  ⟨into (normalized x),⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

theorem word (x : U32) :
    NEB_AdditiveRef.normalize_word x=ok (AspisS1M31Embedding.Total.reduce x) := by
  rw [NEB_WordRefs.normalize]
  exact AspisS1M31Embedding.Total.rem_total x

theorem canonical (x : NQ) : canonQ (normalized x) := by
  have c (w : U32) : (AspisS1M31Embedding.Total.reduce w).val<2147483647 := by
    rw [AspisS1M31Embedding.Total.reduce_val]
    exact Nat.mod_lt _ (by decide)
  exact ⟨⟨c _,c _⟩,⟨c _,c _⟩⟩

/-- Same raw input words and exact full record across the two emitted carriers. -/
theorem canonical_calls (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31 (into x)=
      ok (into (normalized x)) ∧
    NEB_AdditiveRef.normalize_word x.c0.a=ok (normalized x).c0.a ∧
    NEB_AdditiveRef.normalize_word x.c0.b=ok (normalized x).c0.b ∧
    NEB_AdditiveRef.normalize_word x.c1.a=ok (normalized x).c1.a ∧
    NEB_AdditiveRef.normalize_word x.c1.b=ok (normalized x).c1.b := by
  have r (w : U32) : w%2147483647#u32=ok (AspisS1M31Embedding.Total.reduce w) :=
    AspisS1M31Embedding.Total.rem_total w
  refine ⟨?_,?_,word _,word _,word _,word _⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.canonical_qm31,
      FIo_Native.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
      FIo_Native.aspis_core.field.P,r,bind_tc_ok,normalized]
  · simp only [AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31,
      AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
      AspisS1M31Embedding.aspis_core.field.P,into,r,bind_tc_ok,normalized]

theorem canonical_frame {S Event : Type} (state : S) (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    canonQ (normalized x) ∧
    NEB_PureFrame.run (Event:=Event) state
      (FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x)=ok (normalized x,state,[]) :=
  ⟨(canonical_calls x).1,canonical x,NEB_PureFrame.successful state _ _ (canonical_calls x).1⟩

theorem embedding_call (x : NQ) :
    AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x)=ok (embedded x) := by
  simpa only [into,embedded,normalized] using NBG_Embedding.from_qm31_result (into x)

theorem embedding_frame {S Event : Type} (state : S) (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    canonQ (normalized x) ∧
    AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x)=ok (embedded x) ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x))=
        ok (embedded x,state,[]) :=
  ⟨(canonical_calls x).1,canonical x,embedding_call x,
    NEB_PureFrame.successful state _ _ (embedding_call x)⟩

theorem limbs_frame {S Event : Type} (state : S) (x : NE) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x=ok (wordsE x) ∧
    NEB_PureFrame.run (Event:=Event) state
      (FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x)=ok (wordsE x,state,[]) :=
  ⟨rfl,NEB_PureFrame.successful state _ _ rfl⟩

#print axioms word
#print axioms canonical
#print axioms canonical_calls
#print axioms canonical_frame
#print axioms embedding_call
#print axioms embedding_frame
#print axioms limbs_frame
end NEB_WideRepresentation
end
