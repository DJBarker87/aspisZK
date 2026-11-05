import NHT_PacketOps
import NHT_Tx2AuthModel
set_option autoImplicit false
noncomputable section
namespace NHT_PacketAuth
open Aeneas Aeneas.Std Result VTop_Stages
/-- Auth driver with CLOSED powers/query/flush installed. Every remaining
external member is the same named base operation on both sides. -/
theorem source (base : Ops) (qbase : AspisR1.Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H) :
 NHT_EmittedAuth.tx2_authenticated (NHT_PacketOps.installed base qbase qPlace gPlace)
   D pub proof checkpoint hash none =
 verifier.candidate.tx2_authenticated (NHT_PacketOps.installed base qbase qPlace gPlace)
   D pub proof checkpoint hash none :=
 NHT_Tx2AuthModel.source (NHT_PacketOps.installed base qbase qPlace gPlace)
   D pub proof checkpoint hash none
#print axioms source
end NHT_PacketAuth
