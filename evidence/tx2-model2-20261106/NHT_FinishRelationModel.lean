import NHQ_FinishFrames
import NHT_BindOn
set_option autoImplicit false
noncomputable section
namespace NHT_FinishRelationModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl NHQ_FinishRelationModel
variable {W : Type}

/-- Model tail with the CLOSED dot packet installed on the SAME accumulator. -/
def afterPairPacket (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (weights : Slice NHE_DotBody.NQ) (claim : E) (reply : R E) : Result (R Unit) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | .Continue pair =>
   ops.op0 16#u16 0#usize pair
   ops.op0 16#u16 1#usize claim
   let different ← ops.ne pair claim
   if different then ok (.Err .Relation)
   else
     ops.op1 obs .Relation
     let dot ← NHQ_PacketPorts.dot v.final_message weights
     afterDotReply ops v p a obs dot
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

theorem after_pair (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (weights : Slice NHE_DotBody.NQ) (width : weights.val.length≤64)
 (same : a.weights.deref=SAG_DotAdapter.mapSlice NHE_DotRead.stageQ weights)
 (native_dot : ops.op4 v.final_message a.weights.deref =
   SAG_DotClosed.source v.final_message a.weights.deref)
 (claim : E) (reply : R E) :
 afterPairReply ops v p a obs claim reply =
 afterPairPacket ops v p a obs weights claim reply := by
 have dot := NHQ_FinishPackets.dot_substitute ops v p a obs weights width same native_dot
 cases reply with
 | Err e => rfl
 | Ok pair =>
   unfold afterPairReply afterPairPacket
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
   simp only [dot]

/-- NHM's interface: the full Result on the actual returned weights and SAME
alpha/message/kappa, with no premise that pair succeeds or equals the claim. -/
def PairLaw (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (weights : W) (alpha : Slice E) (packet : Result (R E)) : Prop :=
 ops.op2 weights alpha v.final_message p.kappa=packet

theorem pair_frame (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (weights : W) (alpha : Slice E) (claim : E) (packet : Result (R E))
 (NHM_pair : PairLaw ops v p weights alpha packet) :
 (do let reply ← ops.op2 weights alpha v.final_message p.kappa
     afterPairReply ops v p a obs claim reply) =
 (do let reply ← packet;afterPairReply ops v p a obs claim reply) := by rw [NHM_pair]

/-- CLOSED round/polynomial packet at each exact staged cut. Canonicality of
alpha and index are caller data, never a successful-child premise. -/
theorem round_frame (ops : Ops W) (r : NP6_StdModel.Reservation)
 (bytes : Slice U8) (alpha claim : LPi_FieldValues.NE) (i : Usize)
 (canonicalAlpha : LPi_FieldValues.canonE alpha) (index : i.val<2)
 (native_round : ops.op5 bytes (FIo_Install.fromE alpha) (FIo_Install.fromE claim) i =
  Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) bytes
   (FIo_Install.fromE alpha) (FIo_Install.fromE claim) i)
 (next : R E → Result (R Unit)) :
 (do let reply ← ops.op5 bytes (FIo_Install.fromE alpha) (FIo_Install.fromE claim) i
     next reply) =
 (do let reply ← NHQ_PacketPorts.round bytes alpha claim;next reply) :=
 NHQ_FinishPackets.round_substitute ops r bytes alpha claim i canonicalAlpha index native_round next

/-- Source-shaped frame chain, reused unchanged; new cuts above replace the
actual tail, pair and round calls rather than a chosen successful output. -/
theorem source (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
 Port3_NativeFinishBody.verifier.finish_relation ops v p a obs =
 NHQ_FinishRelationModel.staged ops v p a obs :=
 NHQ_FinishRelationModel.source ops v p a obs
#print axioms after_pair
#print axioms pair_frame
#print axioms round_frame
#print axioms source
end NHT_FinishRelationModel
