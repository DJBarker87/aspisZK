import NDO_JGi_ClaimRead
import NDO_JGi_Y1All
import RPz7_F3M_InactiveCanonical
set_option autoImplicit false
namespace AspisR1.JGi_PreparedClaim
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1ClaimPreparedBridge
open AspisR1CurrentCaller.BorrowedClaimPrepared

theorem source {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (expanded : Slice U8) (pre : r1_wire.Prefix) (sem : r1_semantic.Verified H)
    (view : AspisR1CurrentCaller.verifier.View)
    (gamma kappa : aspis_core.field.WideExact) (powers : Array aspis_core.field.WideExact 29#usize)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre))
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children JGe_Boundaries.value D
      JFs_PublicSerialization.value pre
      (⟨AspisV8R19.SqueezeOracleBridge.encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript H)
      JFm_Begin.challenges none=ok (.Ok sem))
    (viewCall : AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view))
    (y1 : view.y1=JGe_Payload27.value)
    (gcanon : AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE gamma))
    (kcanon : AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE kappa))
    (powersCall : powersPublic 29#usize gamma=ok powers) :
    ∃ claim,closedHashBoundaries.claim D sem (AspisR1CurrentCaller.InstalledPreparation.retainedView view).y1
      (AspisR1CurrentCaller.InstalledPreparation.retainedView view).inactive powers kappa=ok (.Ok claim) := by
  have inactive := F3M_InactiveCanonical.source JFx_NativeBytes.proof expanded JGe_Payload27.value view viewCall
  obtain ⟨cc,ec,bc⟩ := JGi_ClaimArrays.source D expanded pre sem hash expand parse finish
  have reads := JGi_ClaimRead.source sem JGe_Payload27.value cc ec bc JGi_Y1All.source
  have powerCall := powersPublic_success gamma powers powersCall
  obtain ⟨actual,pow,canonical⟩ := AspisR1CurrentPreparedClaim.ClaimPowers.powers_total_exact 29#usize (toClaimE gamma) gcanon
  have same : actual=mapArray toClaimE powers := Result.ok.inj (pow.symm.trans powerCall)
  subst actual
  have weights : ∀ l : Usize,l.val<29 → ∃ x,
      Array.index_usize (mapArray toClaimE powers) l=ok x ∧ AspisR1CurrentPreparedClaim.Concrete.Canonical x := by
    intro l hl
    obtain ⟨x,call,value⟩ := WP.spec_imp_exists
      (Array.index_usize_spec (mapArray toClaimE powers) l
        (by simp only [Array.length,mapArray,List.length_map,powers.property,show (29#usize).val=29 from rfl];exact hl))
    refine ⟨x,call,?_⟩
    rw [value]
    exact (canonical ⟨l.val,hl⟩).1
  have y1' : (AspisR1CurrentCaller.InstalledPreparation.retainedView view).y1=JGe_Payload27.value := y1
  obtain ⟨claim,call,canonical⟩ := JGi_ClaimTotal.source (toClaimDigest D) (toClaimSem sem) JGe_Payload27.value
    (mapArray toClaimE powers) (toClaimE (AspisR1CurrentCaller.InstalledPreparation.retainedView view).inactive)
    (toClaimE kappa) inactive kcanon (fun p hp l hl=>reads p l hp hl) weights
  refine ⟨fromClaimE claim,?_⟩
  change claimPublic D sem _ _ powers kappa=ok (.Ok (fromClaimE claim))
  rw [y1']
  unfold claimPublic
  rw [call,bind_tc_ok]
#print axioms source
end AspisR1.JGi_PreparedClaim
