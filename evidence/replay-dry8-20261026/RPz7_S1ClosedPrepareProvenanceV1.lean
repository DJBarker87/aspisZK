import RPz7_S1OriginalNewStaticFieldsV1
import RPz7_S1WideViewVariantV1
import CurrentCompactPrepareReachabilityV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open OriginalSerializerInstallation

/-- SAME complete compact prepare return supplies its S2 variant, actual View,
semantic child return, exact new/scratch call and static Prepared fields.
No desired variant, chosen semantic value or independent successful child. -/
theorem closed_prepare_provenance (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (closedInstall ops) D pub proof hash none input=ok (.Ok prepared,scratch)) :
    prepared.variant=.S2 ∧
    ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      sourceView proof semantic y1=ok (.Ok view) ∧
      ops.op9 D pub view.semantic hash none=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        D sem view hash input=ok (.Ok prepared,scratch) ∧
      prepared.roots=sem.roots ∧ prepared.semantic_alpha=sem.alpha ∧ prepared.z=sem.z := by
  obtain ⟨semantic,y1,view,sem,hview,hsem,hnew⟩ := PrepareReachability.prepare_success
    (closedInstall ops) D pub proof hash prepared input scratch success
  change sourceView proof semantic y1=ok (.Ok view) at hview
  change originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
    D sem view hash input=ok (.Ok prepared,scratch) at hnew
  have fields := originalNew_static (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
    D sem view hash prepared scratch input hnew
  have variant := sourceView_variant proof semantic y1 view hview
  exact ⟨fields.1.trans variant,semantic,y1,view,sem,hview,hsem,hnew,
    fields.2.1,fields.2.2.1,fields.2.2.2⟩

theorem closed_prepare_variant (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (closedInstall ops) D pub proof hash none input=ok (.Ok prepared,scratch)) :
    prepared.variant=.S2 := (closed_prepare_provenance ops D pub proof hash prepared input scratch success).1

#print axioms closed_prepare_provenance
#print axioms closed_prepare_variant
end AspisR1CurrentCaller.BorrowedClaimPrepared
