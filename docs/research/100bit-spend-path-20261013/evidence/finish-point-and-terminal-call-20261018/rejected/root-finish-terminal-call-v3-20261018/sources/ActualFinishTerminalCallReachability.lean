import ExtractedVerifyFinishReachability

/-! Recover the exact terminal call input from a successful actual finish.
Together with `FinishCalls.finish_success`, this exposes both the semantic
round alpha source and the alpha passed to the public terminal implementation. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.ActualFinishTerminalCallReachability

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem terminal_call_success_of_finish_success
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges)
    (obs : Option (AspisR1PublicPreparation.verifier.Phase → Result Unit))
    (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (hfinish : AspisR1PublicPreparation.FinishModel.finish
      R B D pub pre before challenges obs = ok (.Ok out)) :
    ∃ running afterRounds claims terminal,
      AspisR1PublicPreparation.RoundModel.rounds R D pre before =
        ok (.Ok (running, out.alpha, afterRounds)) ∧
      B.claims pre = ok (.Ok claims) ∧
      B.terminal pub claims out.alpha challenges = ok (.Ok terminal) := by
  obtain ⟨running, afterRounds, record25, record26, z0, after25, z1, after26,
      hrounds, hchallenges, hstate, htranscript, hclaims, hrecord25, hextra,
      hcircle25, hrecord26, hbeforeZ1, hcircle26, hz⟩ :=
    AspisR1PublicPreparation.FinishCalls.finish_success R B D pub pre before
      challenges obs out hfinish
  have h := hfinish
  unfold AspisR1PublicPreparation.FinishModel.finish at h
  rw [hrounds] at h
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
    AspisR1PublicPreparation.VerifyPrefix.mark] at h
  rw [hclaims] at h
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch] at h
  obtain ⟨terminalResult, hterminal, h⟩ := bind_success _ _ _ h
  cases terminalResult with
  | Err e =>
      simp only [core.result.Result.map_err,
        AspisR1PublicPreparation.FinishModel.closureFn11,
        AspisR1PublicPreparation.FinishModel.closureFn10,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
  | Ok terminal =>
      exact ⟨running, afterRounds, out.claims, terminal, hrounds, hclaims, hterminal⟩

#print axioms terminal_call_success_of_finish_success
end AspisR1PublicPreparation.ActualFinishTerminalCallReachability
