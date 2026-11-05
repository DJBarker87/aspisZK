import NHS_PreparedPacket
import NFW_Invert
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_FinishFields
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
-- Source inversion follows the NGU_JGi_FinishFields staged elimination, but
-- exports new alpha/circle producer facts; its claim facts are reused there.
theorem source (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (h : FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)) :
    ∃ (running : aspis_core.field.QM31)
      (t25 t26 t27 : r1_wire.SemanticTranscript H)
      (record25 record26 : r1_wire.ValidatedRecord)
      (z0 z1 : aspis_core.circle.SecureCirclePoint),
      RoundModel.rounds R D pre before=ok (.Ok (running,out.alpha,t25)) ∧
      pre.validated_record 25#u8=ok (.Ok record25) ∧
      FinishModel.circle_validated B D t25 record25=ok (.Ok z0,t26) ∧
      pre.validated_record 26#u8=ok (.Ok record26) ∧
      FinishModel.circle_validated B D t26 record26=ok (.Ok z1,t27) ∧
      out.z=Array.make 2#usize [z0,z1] := by
  unfold FinishModel.finish at h
  obtain ⟨roundsResult, hrounds, h⟩ := NFW_Invert.bind _ _ _ h
  cases roundsResult with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at h
    cases h
  | Ok val =>
    rcases val with ⟨running,alpha,t25⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,VerifyPrefix.mark] at h
    obtain ⟨claimsResult,hclaims,h⟩ := NFW_Invert.bind _ _ _ h
    cases claimsResult with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at h
      cases h
    | Ok claims =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨terminalResult,hterminal,h⟩ := NFW_Invert.bind _ _ _ h
      cases terminalResult with
      | Err e =>
        simp only [AspisR1PublicPreparation.core.result.Result.map_err,FinishModel.closureFn11,FinishModel.closureFn10,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at h
        cases h
      | Ok terminal =>
        simp only [AspisR1PublicPreparation.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
          bind_tc_ok,VerifyPrefix.mark] at h
        obtain ⟨mask16,hm16,h⟩ := NFW_Invert.bind _ _ _ h
        obtain ⟨mask10,hm10,h⟩ := NFW_Invert.bind _ _ _ h
        obtain ⟨claim0,hc0,h⟩ := NFW_Invert.bind _ _ _ h
        obtain ⟨claim27,hc27,h⟩ := NFW_Invert.bind _ _ _ h
        obtain ⟨mask,hm,h⟩ := NFW_Invert.bind _ _ _ h
        obtain ⟨record25Result,hr25,h⟩ := NFW_Invert.bind _ _ _ h
        cases record25Result with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from,bind_tc_ok] at h
          cases h
        | Ok record25 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          obtain ⟨extraResult,hextra,h⟩ := NFW_Invert.bind _ _ _ h
          cases extraResult with
          | Err e =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from,bind_tc_ok] at h
            cases h
          | Ok extra =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            obtain ⟨etaTerminal,het,h⟩ := NFW_Invert.bind _ _ _ h
            obtain ⟨masked,hmasked,h⟩ := NFW_Invert.bind _ _ _ h
            obtain ⟨extra28,he28,h⟩ := NFW_Invert.bind _ _ _ h
            obtain ⟨maskedTerminal,hmt,h⟩ := NFW_Invert.bind _ _ _ h
            obtain ⟨different,hdiff,h⟩ := NFW_Invert.bind _ _ _ h
            cases different with
            | true => cases h
            | false =>
              simp only [VerifyPrefix.mark,r1_wire.SemanticTranscript.impl.state,
                core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
              obtain ⟨pair,hz0,h⟩ := NFW_Invert.bind _ _ _ h
              rcases pair with ⟨circle0Result,t26⟩
              dsimp! only at h
              cases circle0Result with
              | Err e =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from,bind_tc_ok] at h
                cases h
              | Ok z0 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                obtain ⟨record26Result,hr26,h⟩ := NFW_Invert.bind _ _ _ h
                cases record26Result with
                | Err e =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from,bind_tc_ok] at h
                  cases h
                | Ok record26 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                  obtain ⟨beforeZ1Result,hbeforeZ1,h⟩ := NFW_Invert.bind _ _ _ h
                  cases beforeZ1Result with
                  | Err e =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from,bind_tc_ok] at h
                    cases h
                  | Ok beforeZ1 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                    obtain ⟨pair,hz1,h⟩ := NFW_Invert.bind _ _ _ h
                    rcases pair with ⟨circle1Result,t27⟩
                    dsimp! only at h
                    cases circle1Result with
                    | Err e =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from,bind_tc_ok] at h
                      cases h
                    | Ok z1 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,VerifyPrefix.mark] at h
                      obtain ⟨equal,hequal,h⟩ := NFW_Invert.bind _ _ _ h
                      cases equal with
                      | true => cases h
                      | false =>
                        obtain ⟨rootResult,hroot,h⟩ := NFW_Invert.bind _ _ _ h
                        cases rootResult with
                        | Err e =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from,bind_tc_ok] at h
                          cases h
                        | Ok rootPayload =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
                          obtain ⟨copied,hcopy,h⟩ := NFW_Invert.bind _ _ _ h
                          obtain ⟨root2,hroot2,h⟩ := NFW_Invert.bind _ _ _ h
                          have he := core.result.Result.Ok.inj (Result.ok.inj h)
                          cases he
                          exact ⟨running,t25,t26,t27,record25,record26,z0,z1,hrounds,hr25,hz0,hr26,hz1,rfl⟩

#print axioms source
end AspisR1.NHS_FinishFields
