import NHQ_FinishRelationModel
import NHQ_PacketPorts
import NHQ_RoundDomain
set_option autoImplicit false
noncomputable section
namespace NHQ_FinishPackets
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl NHQ_FinishRelationModel
variable {W : Type}

/-- Installing the CLOSED round law preserves every continuation, including error paths. -/
theorem round_substitute (ops : Ops W) (r : NP6_StdModel.Reservation)
 (bytes : Slice U8) (alpha claim : LPi_FieldValues.NE) (i : Usize)
 (canonicalAlpha : LPi_FieldValues.canonE alpha) (index : i.val<2)
 (slot : ops.op5 bytes (FIo_Install.fromE alpha) (FIo_Install.fromE claim) i =
  Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) bytes
   (FIo_Install.fromE alpha) (FIo_Install.fromE claim) i)
 (next : R E → Result (R Unit)) :
 (do let reply ← ops.op5 bytes (FIo_Install.fromE alpha) (FIo_Install.fromE claim) i
     next reply) =
 (do let reply ← NHQ_PacketPorts.round bytes alpha claim
     next reply) := by
 rw [slot,←NHQ_PacketPorts.round_packet r bytes alpha claim i canonicalAlpha index]

/-- The packet is on the SAME post-flush weight slice; width is caller-established. -/
theorem dot_substitute (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (weights : Slice NHE_DotBody.NQ) (width : weights.val.length≤64)
 (same : a.weights.deref=SAG_DotAdapter.mapSlice NHE_DotRead.stageQ weights)
 (slot : ops.op4 v.final_message a.weights.deref = SAG_DotClosed.source v.final_message a.weights.deref) :
 (do let reply ← ops.op4 v.final_message a.weights.deref
     afterDotReply ops v p a obs reply) =
 (do let reply ← NHQ_PacketPorts.dot v.final_message weights
     afterDotReply ops v p a obs reply) := by
 rw [slot,same,←NHQ_PacketPorts.dot_packet v.final_message weights width]

/-- NHM's future full-Result packet is applied at the actual pair continuation. -/
theorem pair_substitute (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (weights : W) (alpha : Slice E) (claim : E) (packet : Result (R E))
 (NHM_pair : ops.op2 weights alpha v.final_message p.kappa=packet) :
 (do let reply ← ops.op2 weights alpha v.final_message p.kappa
     afterPairReply ops v p a obs claim reply) =
 (do let reply ← packet
     afterPairReply ops v p a obs claim reply) := by rw [NHM_pair]

#print axioms round_substitute
#print axioms dot_substitute
#print axioms pair_substitute
end NHQ_FinishPackets
