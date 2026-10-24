import S1PreparedSourceStaticFieldsV1
import S1ClosedPreparationInstallationV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (success : (m >>= k)=ok out) : ∃ value,m=ok value ∧ k value=ok out := by
  cases m with
  | ok value => exact ⟨value,rfl,success⟩
  | fail error => cases success
  | div => cases success

/-- Full current original Prepared.new return preserves all static fields.
No variant/root/semantic equality is assumed, and the SAME returned scratch
is used in the successful source call rather than supplied independently. -/
theorem originalNew_static (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (view : verifier.View) (hash : H) (prepared : verifier.Prepared)
    (scratch input : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : originalNew sampling embed D sem view hash input=ok (.Ok prepared,scratch)) :
    prepared.variant=view.variant ∧ prepared.roots=sem.roots ∧
      prepared.semantic_alpha=sem.alpha ∧ prepared.z=sem.z := by
  rw [originalNew_eq_transport] at success
  obtain ⟨pair,hprepare,hout⟩ := bind_success _ _ _ success
  rcases pair with ⟨result,g⟩
  cases result with
  | Err error => cases hout
  | Ok source =>
    have preparedEq := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj hout))
    rw [←preparedEq]
    have fields := AspisR1PublicPreparation.PreparedScratchReachability.prepare_static
      _ _ _ _ _ source g _ hprepare
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [currentPrepared,retainedView,OriginalPreparedSource.variant_round]
        using congrArg currentVariant fields.1
    · simpa only [currentPrepared,retainedSem] using fields.2.1
    · simpa only [currentPrepared,retainedSem,OriginalPreparedSource.q_array_round_current]
        using congrArg (mapArray currentQ) fields.2.2.1
    · simpa only [currentPrepared,retainedSem,OriginalPreparedSource.point_array_round_current]
        using congrArg (mapArray currentPoint) fields.2.2.2

#print axioms originalNew_static
end AspisR1CurrentCaller.BorrowedClaimPrepared
