import NDO_JHm_ClaimEvaluation
import NDO_JHm_RetainedOperands
import NDO_JHm_ClaimPublicCall
import NDO_JHm_ClaimCarriers
import NDO_JHm_InactiveZero
import RPz7_F3M_InactiveCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_PreparedClaim
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition BorrowedClaimPrepared AspisR1ClaimPreparedBridge JGr_Geometry

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    Tx1Q_Carriers.e p.claim=JFq_Claim.scalar := by
  obtain ⟨initial,expanded,sem,view,gamma,kappa,claim,powers,expand,wide,verify,powerCall,claimCall,pg,pk,pc⟩ :=
    JHm_ClaimOperands.source p input scratch prepare
  obtain ⟨before,beforeCall,claims,extra,beforeEq⟩ :=
    JHm_RetainedOperands.source initial expanded sem expand verify
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have eg : toClaimE gamma=JHm_ClaimCarriers.gamma := by
    rw [←JHm_ClaimCarriers.gammaNative]
    change JHm_ClaimCarriers.native (Tx1Q_Carriers.e (currentE gamma))=_
    rw [←pg,fields.1]
  have ek : toClaimE kappa=JHm_ClaimCarriers.kappa := by
    rw [←JHm_ClaimCarriers.kappaNative]
    change JHm_ClaimCarriers.native (Tx1Q_Carriers.e (currentE kappa))=_
    rw [←pk,fields.2.1]
  have gc : AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE gamma) :=
    eg.symm ▸ JHm_ClaimCarriers.gammaCanonical
  have kc : AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE kappa) :=
    ek.symm ▸ JHm_ClaimCarriers.kappaCanonical
  obtain ⟨other,viewCall,variant,y1,round0,folded,round1,finalMessage,inactive⟩ := JGg_ViewOpening.source expanded
  have same : other=view := core.result.Result.Ok.inj (Result.ok.inj (viewCall.symm.trans wide))
  subst other
  have payload : (retainedView view).y1=JGe_Payload27.value := y1
  have ic := F3M_InactiveCanonical.source _ _ _ view wide
  have iv := JHm_InactiveZero.source expanded view wide
  have gp := powersPublic_success gamma powers powerCall
  obtain ⟨out,run,outEq⟩ := JHm_ClaimPublicCall.source _ _ _ _ _ claim powers claimCall
  have numeric := JHm_ClaimEvaluation.source _ _ _ _ _ _ out _ gc kc ic gp run
    (by rw [eg];exact JHm_Arithmetic.gamma_value)
    (by rw [ek];rfl) iv ?_
  · have sameOut : out=JHm_ClaimCarriers.claim :=
      JHm_ClaimCarriers.unique out JHm_ClaimCarriers.claim numeric.1 JHm_ClaimCarriers.claimCanonical
        (numeric.2.trans (JHm_ClaimCarriers.decodeNative JFq_Claim.scalar).symm)
    rw [pc,←outEq,sameOut]
    rfl
  · intro point j hp hj q selected
    have h := JHm_SelectedNumeric.source (toClaimSem (retainedSem sem)) _ before
      claims extra beforeEq beforeCall payload point j hp hj q selected
    have bound : j.val<(JHm_Arithmetic.row point.val).length := by
      rw [JHm_RowFacts.length (⟨point.val,hp⟩ : Fin 6)];exact hj
    simpa only [List.getD_eq_getElem _ 0 bound] using h
#print axioms source
end AspisR1.JHm_PreparedClaim
end
