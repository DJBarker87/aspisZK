import CurrentPreparedScratchReachability
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedScratchReachability
open Aeneas Aeneas.Std Result

/-- Original preparation's SAME successful output preserves the View variant
and every static semantic field. No canonicality or backend success premise. -/
theorem afterQueries_static {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View)
    (gamma kappa : aspis_core.field.WideExact) (alpha : Array aspis_core.field.WideExact 2#usize)
    (row : U8) (before : transcript.Transcript H) (prepared : verifier.Prepared)
    (scratch : Array aspis_core.field.WideExact 29#usize)
    (reached : AfterQueries B D sem view gamma kappa alpha row before prepared scratch) :
    prepared.variant=view.variant ∧ prepared.roots=sem.roots ∧
      prepared.semantic_alpha=sem.alpha ∧ prepared.z=sem.z := by
  obtain ⟨queries,after,last,rho,claim,hq,hr,hpowers,hclaim,hout⟩ := reached
  rw [hout]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem tail_static {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View)
    (gamma kappa alpha0 : aspis_core.field.WideExact) (before : transcript.Transcript H)
    (prepared : verifier.Prepared) (scratch : Array aspis_core.field.WideExact 29#usize)
    (reached : Tail B D sem view gamma kappa alpha0 before prepared scratch) :
    prepared.variant=view.variant ∧ prepared.roots=sem.roots ∧
      prepared.semantic_alpha=sem.alpha ∧ prepared.z=sem.z := by
  cases reached with
  | single folds tail => exact afterQueries_static _ _ _ _ _ _ _ _ _ _ _ tail
  | double folds root bytes1 bytes2 alpha1 afterAlpha hroot hb1 hb2 ha tail =>
    exact afterQueries_static _ _ _ _ _ _ _ _ _ _ _ tail

theorem prepare_static {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (prepared : verifier.Prepared) (scratch input : Array aspis_core.field.WideExact 29#usize)
    (success : PreparedScratchModel.prepare B D sem view hash input=ok (.Ok prepared,scratch)) :
    prepared.variant=view.variant ∧ prepared.roots=sem.roots ∧
      prepared.semantic_alpha=sem.alpha ∧ prepared.z=sem.z := by
  obtain ⟨start,t1,t2,t3,inactive,gamma,kappa,alpha0,hn,hg,hbytes,hk,ha,tail⟩ :=
    prepare_success B D sem view hash prepared scratch input success
  exact tail_static _ _ _ _ _ _ _ _ _ _ tail

#print axioms afterQueries_static
#print axioms tail_static
#print axioms prepare_static
end AspisR1PublicPreparation.PreparedScratchReachability
