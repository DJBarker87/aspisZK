import NIT_FinishArguments
import NHT_RoundPacket
import NIG_FinishExport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishChildren
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

/-- CLOSED first-round law on the logged decoded alpha/claim. Equality to the
opaque logged reply is NOT assumed or asserted by this law instantiation. -/
theorem round0 (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit)
 (cut : cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out) :
 NHT_RoundPacket.packet v.round0 (l.round_alpha 0) (l.round_claim 0)=
 Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round0 (l.round_alpha 0) (l.round_claim 0) 0#usize := by
 obtain ⟨_,_,same,_⟩ := NIT_FinishArguments.first v p a round0 round1 alpha semanticAlpha z message owner weights l out cut
 have ca := (NIG_FinishAlpha.selected proof v p a domain 0#usize (by decide)).2
 rw [←same] at ca
 exact NHT_RoundPacket.source r v.round0 _ _ 0#usize ca (by decide)

/-- Round1 is instantiated only when the parent's observed count reaches it.
Its claim is the actual previous reply fixed by the parent's own cut. -/
theorem round1 (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit)
 (cut : cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out)
 (reached : 2≤l.count) :
 l.round_reply 0=.Ok (l.round_claim 1) ∧
 NHT_RoundPacket.packet v.round1 (l.round_alpha 1) (l.round_claim 1)=
 Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
  v.round1 (l.round_alpha 1) (l.round_claim 1) 1#usize := by
 obtain ⟨_,_,same,claim⟩ := NIT_FinishArguments.second v p a round0 round1 alpha semanticAlpha z message owner weights l out cut reached
 have ca := (NIG_FinishAlpha.selected proof v p a domain 1#usize (by decide)).2
 rw [←same] at ca
 exact ⟨claim,NHT_RoundPacket.source r v.round1 _ _ 1#usize ca (by decide)⟩

/-- Complete NEW result at the SAME variant and two actual constructor arrays.
No owner, payload or successful return is selected here. -/
theorem new_child (r : NP6_StdModel.Reservation) (p : verifier.Prepared) :
 (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=
 FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z :=
 NIG_FinishExport.NHM_new r p

#print axioms round0
#print axioms round1
#print axioms new_child
end AspisR1.NIW_AlignFinishChildren
