import NEB_RepresentationRefs
set_option autoImplicit false
noncomputable section
namespace NEB_EmbeddingDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_WideRepresentation

def Canonical (x : EE) : Prop :=
  ((x.c0.c0.a.val<2147483647 ∧ x.c0.c0.b.val<2147483647) ∧
   (x.c0.c1.a.val<2147483647 ∧ x.c0.c1.b.val<2147483647)) ∧
  ((x.c1.c0.a.val<2147483647 ∧ x.c1.c0.b.val<2147483647) ∧
   (x.c1.c1.a.val<2147483647 ∧ x.c1.c1.b.val<2147483647))

theorem canonical_output (x : NQ) : Canonical (embedded x) := by
  have c := NEB_WideRepresentation.canonical x
  have zero : (0#u32).val<2147483647 := by decide
  exact ⟨c,⟨⟨zero,zero⟩,⟨zero,zero⟩⟩⟩

/-- Callee selected PacketDomain is every raw four-limb word. Its exact
emitted carrier and the returned canonical carrier are derived at this call. -/
theorem canonical_edge (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31 (into x)=
      ok (into (normalized x)) ∧
    NEB_RepresentationRef.canonical (NEB_RepresentationRefs.q x)=
      ok (NEB_RepresentationRefs.q (normalized x)) ∧
    AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x)=ok (embedded x) ∧
    Canonical (embedded x) :=
  ⟨(canonical_calls x).1,(canonical_calls x).2.1,NEB_RepresentationRefs.canonical x,
    embedding_call x,canonical_output x⟩

#print axioms canonical_output
#print axioms canonical_edge
end NEB_EmbeddingDomain
end
