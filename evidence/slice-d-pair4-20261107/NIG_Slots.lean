import NGK_COMBINED_IMPORT
import NHT_FinishRelationModel
set_option autoImplicit false
noncomputable section
namespace NIG_Slots
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody
abbrev W:=FIo_Install.W

def installed (r:NP6_StdModel.Reservation):Ops W:=Port4D_Round.native (IDa_Deployed.finish r)

theorem NHM_new (r:NP6_StdModel.Reservation) (p:verifier.Prepared):
 (installed r).op3 p.variant p.semantic_alpha p.z=
 FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z:=rfl

theorem NHM_pair (r:NP6_StdModel.Reservation) (p:verifier.Prepared) (v:verifier.View):
 ∀ weights,(installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok weights)→
 ∀ alpha,core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.wide_exact.WideExact)) p.alpha {«end»:=2#usize}=ok alpha→
 NHT_FinishRelationModel.PairLaw (installed r) v p weights alpha
  (FIo_Install.pair r weights alpha v.final_message p.kappa):=by
 intro weights from_new alpha from_prefix
 rfl

theorem dot (r:NP6_StdModel.Reservation) (f:Slice U8) (weights:Slice aspis_core.field.QM31):
 (installed r).op4 f weights=SAG_DotClosed.source f weights:=rfl

theorem folds (r:NP6_StdModel.Reservation) (p:verifier.Prepared) (s2:p.variant=.S2):
 (installed r).op6 p.variant=ok 2#usize:=by rw [s2];rfl

theorem release (r:NP6_StdModel.Reservation):
 Port3_FinishStage.release (IDa_Deployed.finish r)=IDa_Deployed.finish r:=rfl

theorem round0 (r:NP6_StdModel.Reservation) (f:Slice U8) (alpha claim:aspis_core.field.wide_exact.WideExact):
 (installed r).op5 f alpha claim 0#usize=
 Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) f alpha claim 0#usize:=by
 change Port4D_Round.round (Port3_FinishStage.release (IDa_Deployed.finish r)) f alpha claim 0#usize=_
 rw [release]
 exact Port4D_Round.round_zero _ _ _ _

theorem round1 (r:NP6_StdModel.Reservation) (f:Slice U8) (alpha claim:aspis_core.field.wide_exact.WideExact):
 (installed r).op5 f alpha claim 1#usize=
 Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r) f alpha claim 1#usize:=by
 change Port4D_Round.round (Port3_FinishStage.release (IDa_Deployed.finish r)) f alpha claim 1#usize=_
 rw [release]
 exact Port4D_Round.round_one _ _ _ _
#print axioms NHM_new
#print axioms NHM_pair
#print axioms dot
#print axioms folds
#print axioms release
#print axioms round0
#print axioms round1
end NIG_Slots
