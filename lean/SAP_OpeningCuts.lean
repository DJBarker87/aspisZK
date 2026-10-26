import SAP_Cuts
import SAP_CanonicalCarrier
import PAln_OpeningStages
import F3K_SourceQueryDecode
import F3L_RhoCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_OpeningCuts
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning

theorem opening (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input=ok (.Ok p,scratch)) :
    ∃ (expanded y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H)
      (out : AspisR1PublicPreparation.verifier.Prepared)
      (rs : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      sourceView proof expanded y1=ok (.Ok view) ∧ view.semantic=expanded ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub expanded hash=ok (.Ok sem) ∧
      currentPrepared out=p ∧
      AspisR1PublicPreparation.PreparedScratchReachability.Reachable
        (concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling)
          AspisS1M31Embedding.Total.embed)) (retainedDigest D) (retainedSem sem) (retainedView view) hash out rs ∧
      (AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE out.gamma) ∧
       AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE out.kappa)) ∧
      CanonicalAlphaPair out ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE out.claim) := by
  obtain ⟨stored,initial,expanded,y1,view,sem,read,expand,wide,same,verify,prepare⟩ :=
    SAP_Cuts.buffers ops B std D hash pub proof p input scratch success
  obtain ⟨out,rs,prepared,outEq,scratchEq⟩ := PAln_Borrowed.original_success
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem view hash
    input scratch p prepare
  have meaning := prepared_installed_meaning (withOriginalSerializer closedSampling)
    AspisS1M31Embedding.Total.embed (retainedDigest D) (retainedSem sem) (retainedView view) hash
    out rs (mapArray retainedE input) (F3M_InactiveCanonical.source proof expanded y1 view wide) prepared
  have reached := AspisR1PublicPreparation.PreparedScratchReachability.prepare_success _ (retainedDigest D)
    (retainedSem sem) (retainedView view) hash out rs (mapArray retainedE input) prepared
  obtain ⟨final,hzero,hvalues,canonClaim,polynomial⟩ := meaning.2.2.1
  exact ⟨expanded,y1,view,sem,out,rs,wide,same,verify,outEq,reached,meaning.1,meaning.2.1,canonClaim⟩

#print axioms opening
end AspisR1.SAP_OpeningCuts
end
