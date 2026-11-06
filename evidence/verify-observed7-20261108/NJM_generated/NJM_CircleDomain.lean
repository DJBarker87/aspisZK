import NJM_ChildDomain
set_option autoImplicit false
namespace AspisR1.NJM_CircleDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Complete block Code projection has the same allowed reply domain as the
emitted source, with every failed/diverging digest prefix kept by the Code. -/
theorem code {H : Type} (D : aspis_core.Digest32 H) (t : r1_wire.SemanticTranscript H)
 (row : U8) (framed : Slice U8) :
 NJM_ChildDomain.Good (PreparedHashCode.run (S1SemanticCode.sampleBlock D t row framed)).2 := by
 rw [PreparedHashCode.run_value,S1SemanticCode.sampleBlock_erasure]
 exact NJM_ChildDomain.block D t row framed

theorem reply {H : Type} (D : aspis_core.Digest32 H)
 (before after : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8)
 (reply : NIX_DispatchCut.Reply)
 (call : (PreparedHashCode.run (S1SemanticCode.sampleBlock D before row framed)).2=ok (reply,after)) :
 NIX_DispatchCut.childDomain reply := by
 have good:=code D before row framed
 rw [call] at good
 cases reply with
 | Ok b => trivial
 | Err error => cases error <;> exact good

#print axioms code
#print axioms reply
end AspisR1.NJM_CircleDomain
