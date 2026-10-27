import RPv_FJa_ClaimsRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ClaimsReference
open Aeneas Aeneas.Std Result
open AspisR1ClaimsUnrolledParent
/-- Invert successful reference prefix/allocator branches to its SAME final
three-row decoder call. No allocator contents or canonicality is assumed. -/
theorem reached (ext : External) (pre : r1_wire.Prefix) (out : Claims)
    (run : claimsReference ext pre=ok (.Ok out)) :
    ∃ record : Record,decodeRows ext record=ok (.Ok out) := by
  unfold claimsReference at run
  obtain ⟨r,hr,run⟩ := FIv_Map.bind_success _ _ _ run
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at run
    cases run
  | Ok vr =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
    obtain ⟨q,hq,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨r1,hr1,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨r2,hr2,run⟩ := FIv_Map.bind_success _ _ _ run
    cases r2 with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
      cases run
    | Ok allocated =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨s,hs,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨r3,hr3,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨r4,hr4,run⟩ := FIv_Map.bind_success _ _ _ run
      cases r4 with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at run
        cases run
      | Ok array =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
        exact ⟨vr,run⟩
#print axioms reached
end AspisR1.FJa_ClaimsReference
end
