import NEB_RepresentationRef.Funs
import NEB_WideRepresentation
set_option autoImplicit false
noncomputable section
namespace NEB_RepresentationRefs
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_ArrayRefs NEB_WideRepresentation

def c (x : NC) : NEB_RepresentationRef.C := ⟨x.a,x.b⟩
def q (x : NQ) : NEB_RepresentationRef.Q := ⟨c x.c0,c x.c1⟩
def e (x : NE) : NEB_RepresentationRef.E := ⟨q x.c0,q x.c1⟩
def backQ (x : NEB_RepresentationRef.Q) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def backE (x : NEB_RepresentationRef.E) : NE := ⟨backQ x.c0,backQ x.c1⟩
def embeddingE (x : EE) : NEB_RepresentationRef.E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def backEmbedding (x : NEB_RepresentationRef.E) : EE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem q_roundtrip (x : NQ) : backQ (q x)=x := rfl
theorem e_roundtrip (x : NE) : backE (e x)=x := rfl
theorem embedding_roundtrip (x : EE) : backEmbedding (embeddingE x)=x := rfl

theorem q_injective : Function.Injective q := by
  intro x y h
  exact (q_roundtrip x).symm.trans ((congrArg backQ h).trans (q_roundtrip y))
theorem e_injective : Function.Injective e := by
  intro x y h
  exact (e_roundtrip x).symm.trans ((congrArg backE h).trans (e_roundtrip y))
theorem embedding_injective : Function.Injective embeddingE := by
  intro x y h
  exact (embedding_roundtrip x).symm.trans ((congrArg backEmbedding h).trans (embedding_roundtrip y))

/-- Independent record reference: all four words, arbitrary raw inputs. -/
theorem canonical (x : NQ) :
    NEB_RepresentationRef.canonical (q x)=ok (q (normalized x)) := by
  have rem (w : U32) : w%2147483647#u32=ok (AspisS1M31Embedding.Total.reduce w) := by
    simpa only [AspisS1M31Embedding.aspis_core.field.P] using AspisS1M31Embedding.Total.rem_total w
  simp only [NEB_RepresentationRef.canonical,NEB_RepresentationRef.P,q,c,
    rem,bind_tc_ok,normalized]

theorem embedding (x : NQ) :
    NEB_RepresentationRef.embed (q x)=ok (embeddingE (embedded x)) := by
  simp only [NEB_RepresentationRef.embed,canonical,bind_tc_ok,embeddingE,embedded,into,q,c,normalized]

theorem getter (x : NE) :
    NEB_RepresentationRef.words (e x)=FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x := rfl

theorem canonical_frame {S Event : Type} (state : S) (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    NEB_RepresentationRef.canonical (q x)=ok (q (normalized x)) ∧ canonQ (normalized x) ∧
    NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x)=
      ok (normalized x,state,[]) ∧
    NEB_PureFrame.run (Event:=Event) state (NEB_RepresentationRef.canonical (q x))=
      ok (q (normalized x),state,[]) :=
  ⟨(canonical_calls x).1,canonical x,NEB_WideRepresentation.canonical x,
    NEB_PureFrame.successful state _ _ (canonical_calls x).1,
    NEB_PureFrame.successful state _ _ (canonical x)⟩

theorem embedding_frame {S Event : Type} (state : S) (x : NQ) :
    AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x)=ok (embedded x) ∧
    NEB_RepresentationRef.embed (q x)=ok (embeddingE (embedded x)) ∧
    canonQ (normalized x) ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x))=ok (embedded x,state,[]) ∧
    NEB_PureFrame.run (Event:=Event) state (NEB_RepresentationRef.embed (q x))=
      ok (embeddingE (embedded x),state,[]) :=
  ⟨embedding_call x,embedding x,NEB_WideRepresentation.canonical x,
    NEB_PureFrame.successful state _ _ (embedding_call x),
    NEB_PureFrame.successful state _ _ (embedding x)⟩

theorem getter_frame {S Event : Type} (state : S) (x : NE) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x=ok (wordsE x) ∧
    NEB_RepresentationRef.words (e x)=ok (wordsE x) ∧
    NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x)=
      ok (wordsE x,state,[]) ∧
    NEB_PureFrame.run (Event:=Event) state (NEB_RepresentationRef.words (e x))=ok (wordsE x,state,[]) :=
  ⟨rfl,getter x,NEB_PureFrame.successful state _ _ rfl,NEB_PureFrame.successful state _ _ (getter x)⟩

#print axioms q_roundtrip
#print axioms e_roundtrip
#print axioms embedding_roundtrip
#print axioms q_injective
#print axioms e_injective
#print axioms embedding_injective
#print axioms canonical
#print axioms embedding
#print axioms getter
#print axioms canonical_frame
#print axioms embedding_frame
#print axioms getter_frame
end NEB_RepresentationRefs
end
