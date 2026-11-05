import NHG_Serializer
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NHG_PublicTranscript
abbrev Public := pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Bytes32 := Array U8 32#usize

def computation {H : Type} (D : aspis_core.Digest32 H) (p : Public)
 (hash : H) (root : Bytes32) :
 Result (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error) := do
 let produced ← NHG_Serializer.computation p
 match produced with
 | .Err _ => ok (.Err .Public)
 | .Ok bytes => NGX_SemanticNew.computation D hash (alloc.vec.Vec.deref bytes) root

theorem source {H : Type} (D : aspis_core.Digest32 H) (p : Public)
 (hash : H) (root : Bytes32) :
 r1_semantic.public_transcript D p hash root=computation D p hash root := by
 unfold r1_semantic.public_transcript computation
 rw [←NHG_Serializer.source]
 cases h : p.public_bytes with
 | fail e => rfl
 | div => rfl
 | ok r => cases r with
   | Err e => rfl
   | Ok bytes => exact NGX_SemanticNew.source D hash _ root

/-- Ordered effects use the SAME producer result and the SAME owned Vec's
borrow. Rejection has no digest event, including arbitrary source Public errors. -/
def packetCode {H : Type} (D : aspis_core.Digest32 H) (p : Public)
 (hash : H) (root : Bytes32) :
 Code (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error) := do
 let produced ← NHG_Serializer.computation p
 match produced with
 | .Err _ => pure (.Err .Public)
 | .Ok bytes => S1SemanticCode.newTranscript D hash (alloc.vec.Vec.deref bytes) root

theorem code {H : Type} (D : aspis_core.Digest32 H) (p : Public)
 (hash : H) (root : Bytes32) :
 run (S1SemanticCode.publicTranscript D p hash root)=run (packetCode D p hash root) := by
 unfold S1SemanticCode.publicTranscript packetCode
 rw [←NHG_Serializer.source]
 cases h : p.public_bytes with
 | fail e => simp only [NGX_CodeTrace.lift_bind]
 | div => simp only [NGX_CodeTrace.lift_bind]
 | ok r => cases r <;> simp only [NGX_CodeTrace.lift_bind] <;> rfl

#print axioms source
#print axioms code
end AspisR1.NHG_PublicTranscript
