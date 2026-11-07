import NNG_InstallBase
import NGX_StateImpl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Install
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)

def state {H : Type} (d : aspis_core.digest.Digest32 H) (t : r1_wire.SemanticTranscript H) :=
 AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state (digest d) (toT10 t)
/-- CLOSED146 at the SAME fresh transcript. The complete Result and original
state are exact; the digest method is never called by this occurrence. -/
theorem state_source {H : Type} (d : aspis_core.digest.Digest32 H) (t : r1_wire.SemanticTranscript H) :
 state d t = .ok t.state := NGX_StateImpl.source (digest d) (toT10 t)
#print axioms state_source
end AspisR1.NNG_Install
