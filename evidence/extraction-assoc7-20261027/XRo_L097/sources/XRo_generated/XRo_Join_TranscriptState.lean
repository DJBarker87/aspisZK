import XRo_Join_Installed
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRo_Join_TranscriptState

theorem state {H : Type} (D : C.D H) (t : C.ST H) :
 XRn_Join_Release.r1_wire.SemanticTranscript.impl.state (ed D) (est t) =
 AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state D t := rfl

#print axioms state
end XRo_Join_TranscriptState
