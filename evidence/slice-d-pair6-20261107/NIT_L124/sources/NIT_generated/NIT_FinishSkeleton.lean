import NIT_FinishTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_FinishSkeleton
open Aeneas Aeneas.Std Result NIT_Cuts NIT_FinishComposition AspisR1Stage2

def run (r : NP6_StdModel.Reservation) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) : Result (Reply Unit) :=
 fullBind (NHT_RoundPacket.packet v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim) fun first=>
 fullBind (NHT_RoundPacket.packet v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first) fun claim=>
 fullBind (FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z) fun owner=>do
  let alpha←core.array.Array.index (core.ops.index.IndexSlice
   (core.slice.index.SliceIndexRangeToUsizeSlice FE)) p.alpha {«end»:=2#usize}
  let reply←NIG_PairExport.packet r owner alpha v.final_message p.kappa
  NIT_FinishTail.afterPair r v a (NHQ_WeightPort.weights a.weights.deref) claim reply

/-- The complete NHT Result equation in the exact observed call order. New's
actual successful return supplies pair's owner; round1's claim is round0's
actual return. No independent owner/reply or successful endpoint is assumed. -/
theorem packet (r : NP6_StdModel.Reservation) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) : NIQ_FinishComposition.packet r v p a=run r v p a := by
 unfold NIQ_FinishComposition.packet NHT_FinishRun.run run fullBind
 apply NIT_PairControl.bind_ext
 intro first
 cases first with
 | Err e=>rfl
 | Ok first=>
  unfold NHT_FinishRun.afterFirst
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  apply NIT_PairControl.bind_ext
  intro last
  cases last with
  | Err e=>rfl
  | Ok claim=>
   unfold NHT_FinishChain.afterRound
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,NHT_FinishNewPacket.installed]
   apply NIT_PairControl.bind_ext
   intro owner
   cases owner with
   | Err e=>rfl
   | Ok owner=>
    unfold NHT_FinishChain.afterWeights
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply NIT_PairControl.bind_ext
    intro alpha
    apply NIT_PairControl.bind_ext
    intro reply
    exact NIT_FinishTail.pair r v p a _ claim reply

theorem source (r : NP6_StdModel.Reservation) (proof : Slice U8) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=run r v p a :=
 (NIG_FinishPacket.NHM_finish r proof v p a domain).trans (packet r v p a)

#print axioms packet
#print axioms source
end AspisR1.NIT_FinishSkeleton
