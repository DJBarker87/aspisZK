import NIW_AlignFinishComposed
import NIW_AlignReachedBind
import NIW_AlignFinishErase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishComposedSource
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIT_FinishComposition NIW_AlignFinishComposed Classical

theorem skeleton (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 (run r loc v p a).1=NIT_FinishSkeleton.run r v p a := by
 have ca0 := (NIG_FinishAlpha.selected proof v p a domain 0#usize (by decide)).2
 have ca1 := (NIG_FinishAlpha.selected proof v p a domain 1#usize (by decide)).2
 have law0 : Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
   v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim 0#usize=
   NHT_RoundPacket.packet v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim :=
  (NHT_RoundPacket.source r v.round0 _ p.claim 0#usize ca0 (by decide)).symm
 rw [run,erase_observe,NIT_FinishSkeleton.run,law0]
 apply NIW_AlignReachedBind.congr
 intro first firstCall
 have law1 : Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
   v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first 1#usize=
   NHT_RoundPacket.packet v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first :=
  (NHT_RoundPacket.source r v.round1 _ first 1#usize ca1 (by decide)).symm
 rw [erase_observe,law1]
 apply NIW_AlignReachedBind.congr
 intro claim claimCall
 rw [erase_observe,←NIG_FinishExport.NHM_new r p]
 apply NIW_AlignReachedBind.congr
 intro owner newCall
 have caller := NIT_PairDomain.caller r proof v p a domain owner newCall
 have native := (NIW_AlignPairInstalled.source r ⟨loc.owner,owner⟩ ⟨loc.alpha,p.alpha⟩
  ⟨loc.message,v.final_message⟩ p.kappa loc.ap0 loc.ap1 loc.common loc.low loc.scratch loc.parts caller).1
 have pairLaw : NIT_ErrorTransport.full (detail r loc owner v p).native.1=
  NIG_PairExport.packet r owner p.alpha.to_slice v.final_message p.kappa :=
  native.symm.trans (NIG_PairExport.source r owner p.alpha.to_slice v.final_message p.kappa)
 dsimp only [attach]
 rw [erase_observe,pairLaw,NIG_PairInputs.alpha_prefix,bind_tc_ok]
 unfold fullBind
 apply NIT_PairControl.bind_ext
 intro reply
 cases reply with
 | Err err => rfl
 | Ok value =>
  simp only [NIT_FinishTail.afterPair,fullBind,bind_tc_ok,done]
  split_ifs
  · rfl
  · rw [erase_observe]
    apply NIW_AlignFinishErase.bind_ext
    intro actual
    rfl

theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=
 (run r loc v p a).1 :=
 (NIT_FinishSkeleton.source r proof v p a domain).trans (skeleton r loc proof v p a domain).symm

#print axioms skeleton
#print axioms source
end AspisR1.NIW_AlignFinishComposedSource
