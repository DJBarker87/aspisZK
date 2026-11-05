import NHT_RoundPacket
import NHQ_RoundDomain
set_option autoImplicit false
noncomputable section
namespace NHT_RoundOutput
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev E := aspis_core.field.wide_exact.WideExact
/-- The canonical next claim follows from the SAME returned first-round packet;
a native round1 cut need only cover this actual successful predecessor. -/
theorem canonical (bytes : Slice U8) (alpha claim out : E)
 (ca : LPi_FieldValues.canonE (FIo_Install.toE alpha))
 (returned : NHT_RoundPacket.packet bytes alpha claim=ok (.Ok out)) :
 LPi_FieldValues.canonE (FIo_Install.toE out) := by
 unfold NHT_RoundPacket.packet NHQ_PacketPorts.round FIo_FieldBridge.map at returned
 obtain ⟨reply,native,rest⟩ := Port3_PushFrame.bind_success _ _ _ returned
 cases reply with
 | Err e => cases rest
 | Ok value =>
   have eq : FIo_Install.fromE value=out := core.result.Result.Ok.inj (Result.ok.inj rest)
   subst out
   have canonical := NHQ_RoundDomain.output bytes (FIo_Install.toE alpha)
     (FIo_Install.toE claim) value ca native
   exact canonical
#print axioms canonical
end NHT_RoundOutput
