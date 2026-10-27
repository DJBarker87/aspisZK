import XRk_Association
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRk_PrepareProjection
abbrev E := aspis_core.field.wide_exact.WideExact
/- An accepted compact prepare reaches the SAME Prepared.new result/scratch.
   No independent semantic success or replacement execution is assumed. -/
theorem constructor {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (old scratch : Array E 29#usize) (p : verifier.Prepared)
    (run : verifier.candidate.prepare D pub proof hash obs old=ok (.Ok p,scratch)) :
    ∃ (sem : r1_semantic.Verified H) (v : verifier.View),
      verifier.Prepared.new D sem v hash old=ok (.Ok p,scratch) := by
  unfold verifier.candidate.prepare at run
  obtain ⟨logicalSemantic,_,run⟩ := bind_success _ _ _ run
  obtain ⟨logicalY1,_,run⟩ := bind_success _ _ _ run
  obtain ⟨capacity,_,run⟩ := bind_success _ _ _ run
  obtain ⟨filled,_,run⟩ := bind_success _ _ _ run
  obtain ⟨r,_,run⟩ := bind_success _ _ _ run
  cases r with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok] at run
    cases run
  | Ok buffer =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
    try simp only [lift,bind_tc_ok] at run
    obtain ⟨slices,_,run⟩ := bind_success _ _ _ run
    rcases slices with ⟨⟨semantic,y1⟩,restore⟩
    obtain ⟨offY1,_,run⟩ := bind_success _ _ _ run
    obtain ⟨semanticInput,_,run⟩ := bind_success _ _ _ run
    obtain ⟨r,semanticOut,_,run⟩ := pair_bind_success _ _ _ run
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
      cases run
    | Ok unit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨offInactive,_,run⟩ := bind_success _ _ _ run
      obtain ⟨y1Input,_,run⟩ := bind_success _ _ _ run
      obtain ⟨r,y1Out,_,run⟩ := pair_bind_success _ _ _ run
      cases r with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at run
        cases run
      | Ok unit =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
        obtain ⟨semanticSlice,_,run⟩ := bind_success _ _ _ run
        obtain ⟨y1Slice,_,run⟩ := bind_success _ _ _ run
        obtain ⟨r,_,run⟩ := bind_success _ _ _ run
        cases r with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from,bind_tc_ok] at run
          cases run
        | Ok view =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
          obtain ⟨semanticResult,_,run⟩ := bind_success _ _ _ run
          obtain ⟨r,_,run⟩ := bind_success _ _ _ run
          cases r with
          | Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from,bind_tc_ok] at run
            cases run
          | Ok sem =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
            obtain ⟨unit,_,run⟩ := bind_success _ _ _ run
            exact ⟨sem,view,run⟩

#print axioms constructor
end XRk_PrepareProjection
