import S1ClosedPrepareProvenanceV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open OriginalSerializerInstallation

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (success : (m >>= k)=ok out) : ∃ value,m=ok value ∧ k value=ok out := by
  cases m with
  | ok value => exact ⟨value,rfl,success⟩
  | fail error => cases success
  | div => cases success

/-- The SAME compact source preparation supplies the complete original
Prepared/scratch carriers and all installed sampler/power ranges. The semantic
child is still arbitrary; its own field/root provenance is not assumed here. -/
theorem closed_prepare_ranges (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (closedInstall ops) D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (source : AspisR1PublicPreparation.verifier.Prepared) (g : Array PE 29#usize),
      prepared=currentPrepared source ∧ scratch=mapArray currentE g ∧
      (Canonical (toClaimE source.gamma) ∧ Canonical (toClaimE source.kappa)) ∧
      AspisR1ClaimPreparedBridge.CanonicalAlphaPair source ∧
      (∀ i : Usize, i.val<29 → ∃ value : E,
        Array.index_usize (mapArray toClaimE g) i=ok value ∧
        Canonical value ∧ decode value=decode (toClaimE source.gamma)^i.val) := by
  obtain ⟨variant,semantic,y1,view,sem,hview,hsem,hnew,roots,alpha,coordinates⟩ :=
    closed_prepare_provenance ops D pub proof hash prepared input scratch success
  unfold sourceView at hview
  obtain ⟨r,hr,hview⟩ := bind_success _ _ _ hview
  cases r with
  | Err error => cases hview
  | Ok oldv =>
    have same : selectedView oldv=view := core.result.Result.Ok.inj (Result.ok.inj hview)
    subst view
    rw [originalNew_eq_transport] at hnew
    obtain ⟨pair,hbackend,hnew⟩ := bind_success _ _ _ hnew
    rcases pair with ⟨result,g⟩
    cases result with
    | Err error => cases hnew
    | Ok source =>
      have pairEq := Result.ok.inj hnew
      have preparedEq := core.result.Result.Ok.inj (congrArg Prod.fst pairEq)
      have scratchEq := congrArg Prod.snd pairEq
      rw [retained_selected_view] at hbackend
      have inactive := AspisR1SelectedWideViewV1.wide_view_inactive_canonical proof semantic y1 oldv hr
      obtain ⟨canonical,alpha,claim,powers⟩ := prepared_installed_meaning
        (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        (retainedDigest D) (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView oldv)
        hash source g (mapArray retainedE input) inactive hbackend
      exact ⟨source,g,preparedEq.symm,scratchEq.symm,canonical,alpha,powers⟩

#print axioms closed_prepare_ranges
end AspisR1CurrentCaller.BorrowedClaimPrepared
