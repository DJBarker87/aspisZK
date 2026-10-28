import NBL_PrepareResults
set_option autoImplicit false
namespace AspisR1.NBR_PreparedFields
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedScratchReachability

/-- Complete field inventory for the existing adopted output constructor.
Paired with the native returned-claim and boxed-field position gates. -/
theorem source {H : Type} (sem : r1_semantic.Verified H) (view : verifier.View)
    (gamma kappa : aspis_core.field.WideExact) (alpha : Array aspis_core.field.WideExact 2#usize)
    (rho : aspis_core.field.QM31) (queries : Array U32 22#usize)
    (claim : aspis_core.field.WideExact) (last : transcript.Transcript H) :
    let result := output sem view gamma kappa alpha rho queries claim last
    result.variant=view.variant ∧ result.roots=sem.roots ∧
    result.gamma=gamma ∧ result.kappa=kappa ∧ result.alpha=alpha ∧ result.rho=rho ∧
    result.queries=queries ∧ result.semantic_alpha=sem.alpha ∧ result.z=sem.z ∧
    result.claim=claim ∧ result.state=last.state := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms source
end AspisR1.NBR_PreparedFields
