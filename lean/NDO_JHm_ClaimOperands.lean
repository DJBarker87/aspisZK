import NDO_JHl_ClaimReached
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_ClaimOperands
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge FirstComposition JGr_Geometry

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    ∃ (initial expanded : Slice U8) (sem : r1_semantic.Verified Unit) (view : verifier.View)
      (gamma kappa claim : AspisR1PublicPreparation.aspis_core.field.WideExact)
      (powers : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
        JFw_RealExpansion.stored initial=ok (.Ok (),expanded) ∧
      sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
        digest (toCurrentPublic JFs_PublicSerialization.value) expanded ()=ok (.Ok sem) ∧
      closedHashBoundaries.powers 29#usize gamma=ok powers ∧
      closedHashBoundaries.claim (retainedDigest digest) (retainedSem sem)
        (retainedView view).y1 (retainedView view).inactive powers kappa=ok (.Ok claim) ∧
      p.gamma=currentE gamma ∧ p.kappa=currentE kappa ∧ p.claim=currentE claim := by
  obtain ⟨initial,expanded,view,sem,expand,wide,viewsem,verify,newCall⟩ :=
    JGp_PrepareCuts.source _ _ _ _ () _ p input scratch prepare
  obtain ⟨out,rs,prepared,outEq,scratchEq⟩ := PAln_Borrowed.original_success
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed _ sem view () input scratch p newCall
  have variant := sourceView_variant _ _ _ _ wide
  have oldVariant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant=_
    rw [variant]
    rfl
  have reached := AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
    closedHashBoundaries (retainedDigest digest) (retainedSem sem) (retainedView view) () out rs
    (mapArray retainedE input) prepared
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,gammaCall,serialized,kappaCall,a0Call,rootCall,first,second,a1Call,queryCall,rhoCall,powers,claimed,output⟩ :=
    PAln_OpeningStages.double_of_reached _ _ (retainedSem sem) (retainedView view) () out rs oldVariant reached
  refine ⟨initial,expanded,sem,view,gamma,kappa,claim,rs,expand,wide,verify,powers,claimed,?_,?_,?_⟩
  all_goals rw [←outEq,output];rfl
#print axioms source
end AspisR1.JHm_ClaimOperands
end
