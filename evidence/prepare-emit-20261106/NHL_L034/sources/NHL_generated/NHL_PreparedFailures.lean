import NHL_PreparedRecompose
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PreparedFailures
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NFW_PreparedControl
open NHL_PreparedScalars

theorem query_fail {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet D sem v hash) (error : Error)
 (queries : actual.sampling.queries D packet.opening.transcript packet.opening.row v.final_message=.fail error) :
 NGN_Emitted.prepared actual D sem v hash old=.fail error := by
 rw [NGN_EmittedEq.staged,NHL_OpeningPacket.result D sem v hash packet,bind_tc_ok]
 unfold NGN_Cuts.queryCut
 rw [queries,bind_tc_fail]

theorem query_div {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet D sem v hash)
 (queries : actual.sampling.queries D packet.opening.transcript packet.opening.row v.final_message=.div) :
 NGN_Emitted.prepared actual D sem v hash old=.div := by
 rw [NGN_EmittedEq.staged,NHL_OpeningPacket.result D sem v hash packet,bind_tc_ok]
 unfold NGN_Cuts.queryCut
 rw [queries,bind_tc_div]
#print axioms query_fail
#print axioms query_div
end AspisR1.NHL_PreparedFailures
