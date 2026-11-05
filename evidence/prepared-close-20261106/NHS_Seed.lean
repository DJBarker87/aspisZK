import NHL_OpeningPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_Seed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- The emitted state getter is a symbolic immutable field projection. -/
theorem state {H : Type} (D : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) :
 r1_wire.SemanticTranscript.impl.state D self=ok self.state := by rfl

/-- S0's sole digest call has the fixed29/1/32-byte descriptors; its value is
an existing runtime observation, never a new digest realization assumption. -/
theorem start {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
 (hash : H) (reply : Array U8 32#usize)
 (call : D.digest hash (NFW_Transcript.seedParts sem.transcript.state)=ok reply) :
 r1_wire.SemanticTranscript.impl.state D sem.transcript=ok sem.transcript.state ∧
 transcript.Transcript.new D hash sem.transcript.state .S2=ok (transcript.Transcript.mk reply hash) :=
 ⟨state D sem.transcript,NFW_Transcript.seed D hash sem.transcript.state reply call⟩
#print axioms state
#print axioms start
end AspisR1.NHS_Seed
