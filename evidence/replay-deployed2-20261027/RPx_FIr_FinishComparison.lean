import RPz7_S1SemanticFinishBoundsV1

/-! Recover the terminal comparison enforced by successful finish execution.
All arithmetic and masking boundaries remain explicit source-call witnesses;
the final comparison is proved, rather than assumed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.FIr_FinishComparison
attribute [local instance] Classical.propDecidable

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem qm_eq_source (x y : aspis_core.field.QM31) :
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq x y =
      ok (decide (x = y)) := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases y with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  by_cases ha : a = e <;> by_cases hb : b = f <;>
    by_cases hc : c = g <;> by_cases hd : d = h <;>
    simp [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
      aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
      ha, hb, hc, hd]

theorem qm_ne_false_eq (x y : aspis_core.field.QM31)
    (h : core.cmp.PartialEq.ne.trait_default
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 x y = ok false) :
    x = y := by
  simpa [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31, qm_eq_source] using h

theorem terminal_comparison_of_finish_success
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish R B D pub pre before challenges (RPz7_PhaseIso.observerToFirst obs) = ok (.Ok out)) :
    ∃ running afterRounds terminal mask16 mask10 claim0 claim27 mask
        etaTerminal masked extra28,
      RoundModel.rounds R D pre before = ok (.Ok (running, out.alpha, afterRounds)) ∧
      B.terminal pub out.claims out.alpha challenges = ok (.Ok terminal) ∧
      B.fromFn 16#usize (FinishModel.closureFn9 D) out.claims = ok mask16 ∧
      B.fromFn 10#usize (FinishModel.closureFn5 D) out.claims = ok mask10 ∧
      Array.index_usize out.claims 0#usize = ok claim0 ∧
      Array.index_usize claim0 27#usize = ok claim27 ∧
      B.mask mask16 mask10 claim27 out.alpha = ok mask ∧
      B.mul challenges.eta terminal = ok etaTerminal ∧
      B.add mask etaTerminal = ok masked ∧
      Array.index_usize out.extra 28#usize = ok extra28 ∧
      B.add masked extra28 = ok running := by
  obtain ⟨running, afterRounds, record25, record26, z0, after25, z1, after26,
      hrounds, hchallenges, hstate, htranscript, hclaims, hrecord25, hextra,
      hcircle25, hrecord26, hbeforeZ1, hcircle26, hz⟩ :=
    S1SemanticFinishBounds.finish_success R B D pub pre before challenges (RPz7_PhaseIso.observerToFirst obs) out hfinish
  have h := hfinish
  unfold FinishModel.finish at h
  rw [hrounds] at h
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
    VerifyPrefix.mark] at h
  rw [hclaims] at h
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch] at h
  obtain ⟨terminalResult, hterminal, h⟩ := bind_success _ _ _ h
  cases terminalResult with
  | Err e =>
      simp only [core.result.Result.map_err, FinishModel.closureFn11,
        FinishModel.closureFn10, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
  | Ok terminal =>
      simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
        bind_tc_ok, VerifyPrefix.mark] at h
      obtain ⟨mask16, hm16, h⟩ := bind_success _ _ _ h
      obtain ⟨mask10, hm10, h⟩ := bind_success _ _ _ h
      obtain ⟨claim0, hc0, h⟩ := bind_success _ _ _ h
      obtain ⟨claim27, hc27, h⟩ := bind_success _ _ _ h
      obtain ⟨mask, hm, h⟩ := bind_success _ _ _ h
      rw [hrecord25] at h
      simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch] at h
      rw [hextra] at h
      simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨etaTerminal, het, h⟩ := bind_success _ _ _ h
      obtain ⟨masked, hmasked, h⟩ := bind_success _ _ _ h
      obtain ⟨extra28, he28, h⟩ := bind_success _ _ _ h
      obtain ⟨maskedTerminal, hmt, h⟩ := bind_success _ _ _ h
      obtain ⟨different, hdiff, h⟩ := bind_success _ _ _ h
      cases different with
      | true => cases h
      | false =>
          have heq := qm_ne_false_eq running maskedTerminal hdiff
          exact ⟨running, afterRounds, terminal, mask16, mask10, claim0, claim27,
            mask, etaTerminal, masked, extra28, hrounds, hterminal, hm16, hm10,
            hc0, hc27, hm, het, hmasked, he28,
            hmt.trans (congrArg Result.ok heq.symm)⟩

#print axioms qm_eq_source
#print axioms qm_ne_false_eq
#print axioms qm_eq_source
#print axioms qm_ne_false_eq
#print axioms terminal_comparison_of_finish_success
end AspisR1PublicPreparation.FIr_FinishComparison
