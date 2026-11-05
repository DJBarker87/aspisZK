import NGX_State
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
set_option autoImplicit false
namespace AspisR1.NGX_StateImpl
 theorem source {H : Type} (D : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) :
   r1_wire.SemanticTranscript.impl.state D self = ok self.state := by rfl
 theorem state_effects {H : Type} (D : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) :
   (r1_wire.SemanticTranscript.impl.state D self, self) = (ok self.state, self) := by rfl
#print axioms source
#print axioms state_effects
end AspisR1.NGX_StateImpl
