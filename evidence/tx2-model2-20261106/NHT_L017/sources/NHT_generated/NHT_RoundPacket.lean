import NHQ_PacketPorts
set_option autoImplicit false
noncomputable section
namespace NHT_RoundPacket
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeFinishBody

def packet (bytes : Slice U8) (alpha claim : E) : Result (core.result.Result E verifier.Error) :=
 NHQ_PacketPorts.round bytes (FIo_Install.toE alpha) (FIo_Install.toE claim)

theorem source (r : NP6_StdModel.Reservation) (bytes : Slice U8)
 (alpha claim : E) (i : Usize) (ca : LPi_FieldValues.canonE (FIo_Install.toE alpha))
 (hi : i.val<2) :
 packet bytes alpha claim =
 Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) bytes alpha claim i := by
 simpa only [packet,FIo_Install.from_to] using
  NHQ_PacketPorts.round_packet r bytes (FIo_Install.toE alpha) (FIo_Install.toE claim) i ca hi
#print axioms source
end NHT_RoundPacket
