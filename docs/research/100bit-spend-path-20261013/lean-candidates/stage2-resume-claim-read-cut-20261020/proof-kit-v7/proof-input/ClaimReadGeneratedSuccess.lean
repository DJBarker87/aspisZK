import AspisR1Stage2ResumeSuffix.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2ResumeClaimReadGeneratedSuccess
abbrev SWide := AspisR1Stage2ResumeSuffix.aspis_core.field.WideExact
abbrev SQM := AspisR1Stage2ResumeSuffix.aspis_core.field.QM31
abbrev SReader := AspisR1Stage2ResumeSuffix.verifier.Reader
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
theorem successful_claim_rhs_power_calls
    (bytes : Slice Std.U8) (startAt : Std.Usize)
    (claim rhs : SWide) (power : SQM) (endAt : Std.Usize)
    (h : AspisR1Stage2ResumeSuffix.verifier.resume_read_claim_rhs_power bytes startAt =
      .ok (.Ok (claim, rhs, power, endAt))) :
    ∃ r1 r2 r3,
      AspisR1Stage2ResumeSuffix.verifier.Reader.e
          ({ bytes := bytes, «at» := startAt } : SReader) = .ok (.Ok claim, r1) ∧
      AspisR1Stage2ResumeSuffix.verifier.Reader.e r1 = .ok (.Ok rhs, r2) ∧
      AspisR1Stage2ResumeSuffix.verifier.Reader.k r2 = .ok (.Ok power, r3) ∧
      r3.«at» = endAt := by
  unfold AspisR1Stage2ResumeSuffix.verifier.resume_read_claim_rhs_power at h
  cases hread1 : AspisR1Stage2ResumeSuffix.verifier.Reader.e
      ({ bytes := bytes, «at» := startAt } : SReader) with
  | fail e => simp [hread1] at h
  | div => simp [hread1] at h
  | ok pair1 =>
    rcases pair1 with ⟨result1, r1⟩
    cases result1 with
    | Err e =>
        simp [hread1,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok claimValue =>
      cases hread2 : AspisR1Stage2ResumeSuffix.verifier.Reader.e r1 with
      | fail e => simp [hread1, hread2] at h
      | div => simp [hread1, hread2] at h
      | ok pair2 =>
        rcases pair2 with ⟨result2, r2⟩
        cases result2 with
        | Err e =>
            simp [hread1, hread2,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        | Ok rhsValue =>
          cases hread3 : AspisR1Stage2ResumeSuffix.verifier.Reader.k r2 with
          | fail e => simp [hread1, hread2, hread3] at h
          | div => simp [hread1, hread2, hread3] at h
          | ok pair3 =>
            rcases pair3 with ⟨result3, r3⟩
            cases result3 with
            | Err e =>
                simp [hread1, hread2, hread3,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
            | Ok powerValue =>
              simp [hread1, hread2, hread3,
                core.result.Result.Insts.CoreOpsTry.branch] at h
              simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
                Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨r1, r2, r3, hread1, hread2, hread3, rfl⟩

#print axioms successful_claim_rhs_power_calls
end AspisR1Stage2ResumeClaimReadGeneratedSuccess
