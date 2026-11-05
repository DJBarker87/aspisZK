import NGK_COMBINED_IMPORT
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
set_option autoImplicit false
namespace AspisR1.NGX_State
 theorem value {H : Type} (self : r1_wire.SemanticTranscript H) :
   r1_wire.SemanticTranscript.state self = self.state := by rfl
 theorem frame {H : Type} (self : r1_wire.SemanticTranscript H) :
   (r1_wire.SemanticTranscript.state self, self.hash, self.next_row) =
     (self.state, self.hash, self.next_row) := by rfl
#print axioms value
#print axioms frame
end AspisR1.NGX_State
