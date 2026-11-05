import NIG_FinishAlpha
set_option autoImplicit false
noncomputable section
namespace NIG_FinishExport
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem NHM_finish (r:NP6_StdModel.Reservation) (proof:Slice U8)
 (v:verifier.View) (p:verifier.Prepared) (a:verifier.Accumulator)
 (domain:NIG_FinishInput.Domain proof v p a):
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=
 NHT_FinishRun.run (NHT_FinishNewPacket.installed (NIG_Slots.installed r)
  (FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z)) v p a none
  (NHQ_WeightPort.weights a.weights.deref) (FIo_Install.pair r)
  (NIG_FinishAlpha.alpha p 0 (by decide)) (NIG_FinishAlpha.alpha p 1 (by decide)):=by
 obtain ⟨i0,c0⟩:=NIG_FinishAlpha.selected proof v p a domain 0#usize (by decide)
 obtain ⟨i1,c1⟩:=NIG_FinishAlpha.selected proof v p a domain 1#usize (by decide)
 exact NIG_FinishConcrete.NHM_finish r proof v p a domain _ _ i0 i1 c0 c1

/-- Exact NHT op3 slot; no arbitrary dictionary or successful-NEW premise. -/
theorem NHM_new (r:NP6_StdModel.Reservation) (p:verifier.Prepared):
 (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=
 FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z:=NIG_Slots.NHM_new r p

/-- Exact NHT op2 equation, on SAME owner and SAME prefix returned by source. -/
theorem NHM_pair (r:NP6_StdModel.Reservation) (p:verifier.Prepared) (v:verifier.View):
 ∀ w,(NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok w)→
 ∀ alpha,core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.wide_exact.WideExact)) p.alpha {«end»:=2#usize}=ok alpha→
 NHT_FinishRelationModel.PairLaw (NIG_Slots.installed r) v p w alpha
  (FIo_Install.pair r w alpha v.final_message p.kappa):=NIG_Slots.NHM_pair r p v
#print axioms NHM_finish
#print axioms NHM_new
#print axioms NHM_pair
end NIG_FinishExport
