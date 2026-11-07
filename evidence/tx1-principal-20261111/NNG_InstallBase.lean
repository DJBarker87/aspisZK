import NNG_Transport_T14
import NMP_ResultTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Install
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Transport
open NMP_ResultTransport (outer inner outer_inverse inner_inverse)
def digest {H : Type} (d : aspis_core.digest.Digest32 H) : AspisR1PublicPreparation.aspis_core.Digest32 H :=
 ⟨d.coremarkerCopyInst,d.digest⟩
end AspisR1.NNG_Install
