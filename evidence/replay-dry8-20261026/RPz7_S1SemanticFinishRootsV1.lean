import RPz7_S1SemanticFinishModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.S1SemanticFinishRoots

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem pair_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok p => cases p with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- SAME successful complete source-shaped finish, including the actual
row-2 payload, full conversion/unwrap results and both returned roots. No root
identity, separate child success or independently chosen root is a premise.
The proof spine is reused verbatim from FinishCalls.finish_success; only the
terminal projection changes. Concrete native child installation remains open. -/
theorem finish_root_calls (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (h : FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)) :
    ∃ (rootPayload : Slice U8)
      (copied : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError)
      (root2 : Array U8 32#usize),
      FinishModel.payload pre 2#u8 = ok (.Ok rootPayload) ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 rootPayload = ok copied ∧
      B.unwrapRoot copied = ok root2 ∧
      out.roots = Array.make 2#usize [pre.c1_root,root2] := by
  unfold FinishModel.finish at h
  obtain ⟨roundsResult, hrounds, h⟩ := bind_success _ _ _ h
  cases roundsResult with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at h
    cases h
  | Ok val =>
    rcases val with ⟨running,alpha,t25⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,VerifyPrefix.mark] at h
    obtain ⟨claimsResult,hclaims,h⟩ := bind_success _ _ _ h
    cases claimsResult with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at h
      cases h
    | Ok claims =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨terminalResult,hterminal,h⟩ := bind_success _ _ _ h
      cases terminalResult with
      | Err e =>
        simp only [core.result.Result.map_err,FinishModel.closureFn11,FinishModel.closureFn10,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at h
        cases h
      | Ok terminal =>
        simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
          bind_tc_ok,VerifyPrefix.mark] at h
        obtain ⟨mask16,hm16,h⟩ := bind_success _ _ _ h
        obtain ⟨mask10,hm10,h⟩ := bind_success _ _ _ h
        obtain ⟨claim0,hc0,h⟩ := bind_success _ _ _ h
        obtain ⟨claim27,hc27,h⟩ := bind_success _ _ _ h
        obtain ⟨mask,hm,h⟩ := bind_success _ _ _ h
        obtain ⟨record25Result,hr25,h⟩ := bind_success _ _ _ h
        cases record25Result with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from,bind_tc_ok] at h
          cases h
        | Ok record25 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          obtain ⟨extraResult,hextra,h⟩ := bind_success _ _ _ h
          cases extraResult with
          | Err e =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from,bind_tc_ok] at h
            cases h
          | Ok extra =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            obtain ⟨etaTerminal,het,h⟩ := bind_success _ _ _ h
            obtain ⟨masked,hmasked,h⟩ := bind_success _ _ _ h
            obtain ⟨extra28,he28,h⟩ := bind_success _ _ _ h
            obtain ⟨maskedTerminal,hmt,h⟩ := bind_success _ _ _ h
            obtain ⟨different,hdiff,h⟩ := bind_success _ _ _ h
            cases different with
            | true => cases h
            | false =>
              simp only [VerifyPrefix.mark,r1_wire.SemanticTranscript.impl.state,
                core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
              obtain ⟨circle0Result,t26,hz0,h⟩ := pair_success _ _ _ h
              cases circle0Result with
              | Err e =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from,bind_tc_ok] at h
                cases h
              | Ok z0 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                obtain ⟨record26Result,hr26,h⟩ := bind_success _ _ _ h
                cases record26Result with
                | Err e =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from,bind_tc_ok] at h
                  cases h
                | Ok record26 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                  obtain ⟨beforeZ1Result,hbeforeZ1,h⟩ := bind_success _ _ _ h
                  cases beforeZ1Result with
                  | Err e =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from,bind_tc_ok] at h
                    cases h
                  | Ok beforeZ1 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                    obtain ⟨circle1Result,t27,hz1,h⟩ := pair_success _ _ _ h
                    cases circle1Result with
                    | Err e =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from,bind_tc_ok] at h
                      cases h
                    | Ok z1 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,VerifyPrefix.mark] at h
                      obtain ⟨equal,hequal,h⟩ := bind_success _ _ _ h
                      cases equal with
                      | true => cases h
                      | false =>
                        obtain ⟨rootResult,hroot,h⟩ := bind_success _ _ _ h
                        cases rootResult with
                        | Err e =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from,bind_tc_ok] at h
                          cases h
                        | Ok rootPayload =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                          obtain ⟨copied,hcopy,h⟩ := bind_success _ _ _ h
                          obtain ⟨root2,hroot2,h⟩ := bind_success _ _ _ h
                          have he := core.result.Result.Ok.inj (Result.ok.inj h)
                          cases he
                          exact ⟨rootPayload,copied,root2,hroot,hcopy,hroot2,rfl⟩


#print axioms finish_root_calls
end AspisR1PublicPreparation.S1SemanticFinishRoots
