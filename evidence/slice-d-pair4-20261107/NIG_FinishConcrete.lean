import NIG_Slots
import NIG_FinishInput
import NHT_FinishPacket
set_option autoImplicit false
noncomputable section
namespace NIG_FinishConcrete
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody
abbrev E:=aspis_core.field.wide_exact.WideExact

theorem NHM_finish (r:NP6_StdModel.Reservation) (proof:Slice U8)
 (v:verifier.View) (p:verifier.Prepared) (a:verifier.Accumulator)
 (domain:NIG_FinishInput.Domain proof v p a) (alpha0 alpha1:E)
 (index0:Array.index_usize p.alpha 0#usize=ok alpha0)
 (index1:Array.index_usize p.alpha 1#usize=ok alpha1)
 (ca0:LPi_FieldValues.canonE (FIo_Install.toE alpha0))
 (ca1:LPi_FieldValues.canonE (FIo_Install.toE alpha1)):
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=
 NHT_FinishRun.run (NHT_FinishNewPacket.installed (NIG_Slots.installed r)
  (FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z)) v p a none
  (NHQ_WeightPort.weights a.weights.deref) (FIo_Install.pair r) alpha0 alpha1:=by
 exact NHT_FinishCaller.source (NIG_Slots.installed r) r v p a none alpha0 alpha1
  index0 index1 ca0 ca1 (NIG_Slots.folds r p domain.s2)
  (NIG_Slots.round0 r _ _ _) (fun claim _=>NIG_Slots.round1 r _ _ _)
  domain.accumulator (NIG_Slots.dot r _ _)
  (FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z)
  (NIG_Slots.NHM_new r p) (FIo_Install.pair r) (NIG_Slots.NHM_pair r p v)

#print axioms NHM_finish
end NIG_FinishConcrete
