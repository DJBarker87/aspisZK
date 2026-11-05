import NIQ_ResultEncoding
import NIQ_PairComposition
import NIG_FinishPacket
set_option autoImplicit false
noncomputable section
namespace NIQ_FinishComposition
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- The unchanged complete finish model, with primitive caller Domain retained.
This is an abbreviation of the exact exported NHT packet, not a native run. -/
abbrev packet (r : NP6_StdModel.Reservation) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) :=
 NHT_FinishRun.run (NHT_FinishNewPacket.installed (NIG_Slots.installed r)
  (FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z)) v p a none
  (NHQ_WeightPort.weights a.weights.deref) (NIG_PairExport.packet r)
  (NIG_FinishAlpha.alpha p 0 (by decide)) (NIG_FinishAlpha.alpha p 1 (by decide))

/-- Error-code projection is lossless on all eight errors, and preserves outer
fail/div. It does not supply the missing Rust local-record interpretation. -/
theorem encoded (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 NIQ_ResultEncoding.full (Port3_NativeFinishBody.verifier.finish_relation
  (NIG_Slots.installed r) v p a none) =
 NIQ_ResultEncoding.full (packet r v p a) :=
 congrArg NIQ_ResultEncoding.full (NIG_FinishPacket.NHM_finish r proof v p a domain)

theorem first_rejected (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) (e : verifier.Error)
 (reply : NHT_RoundPacket.packet v.round0
  (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim = ok (.Err e)) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none =
 ok (.Err e) := by
 rw [NIG_FinishPacket.NHM_finish r proof v p a domain]
 unfold NHT_FinishRun.run
 rw [reply]
 rfl

theorem first_failed (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a)
 (e : Error)
 (reply : NHT_RoundPacket.packet v.round0
  (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim = fail e) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none =
 fail e := by
 rw [NIG_FinishPacket.NHM_finish r proof v p a domain]
 unfold NHT_FinishRun.run
 rw [reply]
 rfl

theorem first_diverged (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a)
 (reply : NHT_RoundPacket.packet v.round0
  (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim = div) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none =
 div := by
 rw [NIG_FinishPacket.NHM_finish r proof v p a domain]
 unfold NHT_FinishRun.run
 rw [reply]
 rfl

#print axioms encoded
#print axioms first_rejected
#print axioms first_failed
#print axioms first_diverged
end NIQ_FinishComposition
