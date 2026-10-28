import JHm_RetainedOperands
import JHm_Row26Numeric
import JHm_Dots
import JHc_InstalledQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_NonVacuity
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition BorrowedClaimPrepared AspisR1ClaimPreparedBridge JGr_Geometry

/-- Auxiliary non-vacuity of the SAME actual preparation and all scalar claim
operands. This does not assert complete headline-hypothesis inhabitance. -/
theorem source : ∃ (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial expanded : Slice U8) (sem : r1_semantic.Verified Unit) (view : verifier.View)
    (gamma kappa claim : AspisR1PublicPreparation.aspis_core.field.WideExact)
    (powers : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize)
    (before : Array AspisR1PublicPreparation.aspis_core.field.QM31 29#usize),
    verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch) ∧
    AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored initial=ok (.Ok (),expanded) ∧
    sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
    S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
      digest (toCurrentPublic JFs_PublicSerialization.value) expanded ()=ok (.Ok sem) ∧
    closedHashBoundaries.powers 29#usize gamma=ok powers ∧
    closedHashBoundaries.claim (retainedDigest digest) (retainedSem sem)
      (retainedView view).y1 (retainedView view).inactive powers kappa=ok (.Ok claim) ∧
    p.gamma=currentE gamma ∧ p.kappa=currentE kappa ∧ p.claim=currentE claim ∧
    Tx1Q_Carriers.e p.gamma=JFq_Gamma.scalar ∧ Tx1Q_Carriers.e p.kappa=JFq_Kappa.scalar ∧
    AspisS1ExtractedRoundChildren.decodeMain 29#usize JFu_Q26Source.record 0#usize=ok (.Ok before) ∧
    (toClaimSem (retainedSem sem)).claims=mapArray (mapArray toClaimQ) JFu_ClaimsData.claims ∧
    (toClaimSem (retainedSem sem)).extra=mapArray toClaimQ JFu_ClaimsData.a3 ∧
    (toClaimSem (retainedSem sem)).before_z1=mapArray toClaimQ before ∧
    before.val.map JHm_RowFacts.scalar=JHm_Arithmetic.row 4 ∧
    (∀ point : Fin 6,JHm_Arithmetic.horner JHm_Arithmetic.gamma (JHm_Arithmetic.row point.val)=
      JHm_Dots.value point.val) := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,prepare,init,pend,geo,query,flush⟩ :=
    JHc_InstalledQuery.inhabited
  obtain ⟨start,expanded,sem,view,gamma,kappa,claim,powers,expand,wide,verify,powerCall,claimCall,pg,pk,pc⟩ :=
    JHm_ClaimOperands.source p _ scratch prepare
  obtain ⟨before,beforeCall,claims,extra,beforeEq⟩ :=
    JHm_RetainedOperands.source start expanded sem expand verify
  have fields := JHa_CurrentFields.source _ _ _ JGn_TerminalIdentified.shaDictionary () p _ scratch prepare
  exact ⟨p,_,scratch,start,expanded,sem,view,gamma,kappa,claim,powers,before,
    prepare,expand,wide,verify,powerCall,claimCall,pg,pk,pc,fields.1,fields.2.1,beforeCall,claims,extra,beforeEq,
    JHm_Row26Numeric.source before beforeCall,JHm_Dots.source⟩
#print axioms source
end AspisR1.JHm_NonVacuity
end
