import NIG_PairExport
import NIG_FinishAlpha
set_option autoImplicit false
noncomputable section
namespace NIG_FinishPacket
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem NHM_finish (r:NP6_StdModel.Reservation) (proof:Slice U8)
 (v:verifier.View) (p:verifier.Prepared) (a:verifier.Accumulator)
 (domain:NIG_FinishInput.Domain proof v p a):
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=
 NHT_FinishRun.run (NHT_FinishNewPacket.installed (NIG_Slots.installed r)
  (FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z)) v p a none
  (NHQ_WeightPort.weights a.weights.deref) (NIG_PairExport.packet r)
  (NIG_FinishAlpha.alpha p 0 (by decide)) (NIG_FinishAlpha.alpha p 1 (by decide)):=by
 obtain ⟨i0,c0⟩:=NIG_FinishAlpha.selected proof v p a domain 0#usize (by decide)
 obtain ⟨i1,c1⟩:=NIG_FinishAlpha.selected proof v p a domain 1#usize (by decide)
 exact NHT_FinishCaller.source (NIG_Slots.installed r) r v p a none _ _ i0 i1 c0 c1
  (NIG_Slots.folds r p domain.s2) (NIG_Slots.round0 r _ _ _)
  (fun claim _=>NIG_Slots.round1 r _ _ _) domain.accumulator (NIG_Slots.dot r _ _)
  (FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z) (NIG_Slots.NHM_new r p)
  (NIG_PairExport.packet r) (NIG_PairExport.NHM_pair r p v)
#print axioms NHM_finish
end NIG_FinishPacket
