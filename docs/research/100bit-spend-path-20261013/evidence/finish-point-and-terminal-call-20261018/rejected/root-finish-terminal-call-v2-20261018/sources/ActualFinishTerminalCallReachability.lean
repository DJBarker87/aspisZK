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
    (obs : _)
    (out : _)
    (hfinish : AspisR1PublicPreparation.FinishModel.finish
      R B D pub pre before challenges obs = ok (.Ok out)) :
    ∃ running afterRounds claims terminal,
      AspisR1PublicPreparation.RoundModel.rounds R D pre before =
        ok (.Ok (running, out.alpha, afterRounds)) ∧
      B.claims pre = ok (.Ok claims) ∧
      B.terminal pub claims out.alpha challenges = ok (.Ok terminal) := by
  unfold AspisR1PublicPreparation.FinishModel.finish at hfinish
  obtain ⟨roundsResult, hroundsRaw, h⟩ := bind_success _ _ _ hfinish
  cases roundsResult with
  | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
  | Ok val =>
      rcases val with ⟨running, alpha, afterRounds⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
        AspisR1PublicPreparation.VerifyPrefix.mark] at h
      obtain ⟨claimsResult, hclaimsRaw, h⟩ := bind_success _ _ _ h
      cases claimsResult with
      | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok] at h
          cases h
      | Ok claims =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          obtain ⟨terminalResult, hterminalRaw, h⟩ := bind_success _ _ _ h
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
              obtain ⟨_run, _t25, _record25, _record26, _z0, _t26, _z1,
                _t27, hroundsOut, _hchallenges, _hstate, _htranscript, _hclaims,
                _hrecord25, _hextra, _hcircle25, _hrecord26, _hbeforeZ1,
                _hcircle26, _hz⟩ :=
                AspisR1PublicPreparation.FinishCalls.finish_success R B D pub pre
                  before challenges obs out hfinish
              have htuple : (running, alpha, afterRounds) =
                  (_run, out.alpha, _t25) := by
                have hcore : core.result.Result.Ok (running, alpha, afterRounds) =
                    core.result.Result.Ok (_run, out.alpha, _t25) := by
                  apply Result.ok.inj
                  exact hroundsRaw.symm.trans hroundsOut
                exact core.result.Result.Ok.inj hcore
              have halpha : alpha = out.alpha :=
                congrArg (fun x : AspisR1PublicPreparation.aspis_core.field.QM31 ×
                  Array AspisR1PublicPreparation.aspis_core.field.QM31 10#usize ×
                  AspisR1PublicPreparation.r1_wire.SemanticTranscript H => x.2.1) htuple
              refine ⟨running, afterRounds, claims, terminal, ?_, hclaimsRaw, ?_⟩
              · simpa [halpha] using hroundsRaw
              · rw [← halpha]
                exact hterminalRaw

#print axioms terminal_call_success_of_finish_success
end AspisR1PublicPreparation.ActualFinishTerminalCallReachability
