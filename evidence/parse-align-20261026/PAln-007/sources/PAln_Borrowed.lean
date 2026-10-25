import PSem_SourceCuts
import CurrentPreparedScratchReachability
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Borrowed
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared

/-- Invert the installed complete source operation. The retained output and
scratch are the ones mapped to the actual returned current carriers. -/
theorem original_success (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result AspisR1ClaimPreparedBridge.PE)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (out : verifier.Prepared)
    (success : originalNew sampling embed D sem v hash input=ok (.Ok out,scratch)) :
    ∃ (retained : AspisR1PublicPreparation.verifier.Prepared)
      (rs : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      AspisR1PublicPreparation.PreparedScratchModel.prepare
        (AspisR1ClaimPreparedBridge.concreteBoundaries
          (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
        (retainedDigest D) (retainedSem sem) (retainedView v) hash
        (AspisR1ClaimPreparedBridge.mapArray retainedE input)=ok (.Ok retained,rs) ∧
      currentPrepared retained=out ∧ AspisR1ClaimPreparedBridge.mapArray currentE rs=scratch := by
  rw [originalNew_eq_transport] at success
  cases call : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      (retainedDigest D) (retainedSem sem) (retainedView v) hash
      (AspisR1ClaimPreparedBridge.mapArray retainedE input) with
  | fail e => simp only [call,bind_tc_fail] at success; cases success
  | div => simp only [call,bind_tc_div] at success; cases success
  | ok pair =>
    rcases pair with ⟨ret,rs⟩
    cases ret with
    | Err e => simp only [call,bind_tc_ok] at success; cases success
    | Ok retained =>
      simp only [call,bind_tc_ok] at success
      have eq := Result.ok.inj success
      exact ⟨retained,rs,call,core.result.Result.Ok.inj (congrArg Prod.fst eq),
        congrArg Prod.snd eq⟩

theorem original_reached (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result AspisR1ClaimPreparedBridge.PE)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (out : verifier.Prepared)
    (success : originalNew sampling embed D sem v hash input=ok (.Ok out,scratch)) :
    ∃ (retained : AspisR1PublicPreparation.verifier.Prepared)
      (rs : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      AspisR1PublicPreparation.PreparedScratchReachability.Reachable
        (AspisR1ClaimPreparedBridge.concreteBoundaries
          (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
        (retainedDigest D) (retainedSem sem) (retainedView v) hash retained rs ∧
      currentPrepared retained=out ∧ AspisR1ClaimPreparedBridge.mapArray currentE rs=scratch := by
  obtain ⟨retained,rs,accepted,outEq,scratchEq⟩ :=
    original_success sampling embed D sem v hash input scratch out success
  exact ⟨retained,rs,
    AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
      _ (retainedDigest D) (retainedSem sem) (retainedView v) hash retained rs
      (AspisR1ClaimPreparedBridge.mapArray retainedE input) accepted,outEq,scratchEq⟩

#print axioms original_reached
#print axioms original_success
end AspisR1.PAln_Borrowed
end
