import CurrentPreparedScratchReachability
set_option autoImplicit false
namespace AspisS1PreparedScratchCalls
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedScratchReachability

/-- The returned Prepared fields identify BOTH actual child calls and their
SAME scratch argument. No independent powers/claim call succeeds by premise. -/
theorem after_queries_calls {H : Type} (B : PreparedScratchModel.Boundaries)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (v : verifier.View)
    (gamma kappa : aspis_core.field.WideExact) (alpha : Array aspis_core.field.WideExact 2#usize)
    (row : U8) (before : transcript.Transcript H) (out : verifier.Prepared)
    (scratch : Array aspis_core.field.WideExact 29#usize)
    (h : AfterQueries B D sem v gamma kappa alpha row before out scratch) :
    B.powers 29#usize out.gamma = ok scratch ∧
    B.claim D sem v.y1 v.inactive scratch out.kappa = ok (.Ok out.claim) := by
  obtain ⟨queries,after,last,rho,claim,query,rhoCall,powers,claimed,same⟩ := h
  rw [same]
  exact ⟨powers,claimed⟩

theorem prepare_calls {H : Type} (B : PreparedScratchModel.Boundaries)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (v : verifier.View)
    (hash : H) (out : verifier.Prepared)
    (scratch input : Array aspis_core.field.WideExact 29#usize)
    (accepted : PreparedScratchModel.prepare B D sem v hash input = ok (.Ok out,scratch)) :
    B.powers 29#usize out.gamma = ok scratch ∧
    B.claim D sem v.y1 v.inactive scratch out.kappa = ok (.Ok out.claim) := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,seed,gammaCall,serialized,
    kappaCall,alphaCall,tail⟩ := prepare_success B D sem v hash out scratch input accepted
  cases tail with
  | single folds h => exact after_queries_calls B D sem v _ _ _ _ _ out scratch h
  | double folds root bytes1 bytes2 alpha1 afterAlpha rootCall firstBytes secondBytes sampled h =>
    exact after_queries_calls B D sem v _ _ _ _ _ out scratch h

#print axioms after_queries_calls
#print axioms prepare_calls
end AspisS1PreparedScratchCalls
