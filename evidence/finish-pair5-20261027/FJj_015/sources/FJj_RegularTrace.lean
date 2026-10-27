import FJg_PairProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_RegularTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE NQ)
abbrev Vec := alloc.vec.Vec NQ

theorem reached [FIo_Native.Allocation] (w : FIo_Native.weights.Weights) (alpha : Slice NE) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Array NE 4#usize)
    (scratch scratchOut : Vec) (before after : Array NE 7#usize)
    (run : FIo_Native.weights.process_regular_kinds w true alpha f folds n ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) :
    ∃ (scratch1 scratch2 : Vec) (parts1 parts2 : Array NE 7#usize),
      FIo_Native.weights.process_kind w 2#usize alpha f folds n ap0 ap1 scratch before=
        ok (.Ok (),scratch1,parts1) ∧
      FIo_Native.weights.process_kind w 5#usize alpha f folds n ap0 ap1 scratch1 parts1=
        ok (.Ok (),scratch2,parts2) ∧
      FIo_Native.weights.process_kind w 6#usize alpha f folds n ap0 ap1 scratch2 parts2=
        ok (.Ok (),scratchOut,after) := by
  unfold FIo_Native.weights.process_regular_kinds at run
  simp only [ite_true] at run
  obtain ⟨⟨r0,s1,p1⟩,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases r0 with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame] at run; cases run
  | Ok u =>
    cases u
    head_reduce run
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
    obtain ⟨⟨r1,s2,p2⟩,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases r1 with
    | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at run; cases run
    | Ok u =>
      cases u
      head_reduce run
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨⟨r2,s3,p3⟩,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases r2 with
      | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame] at run; cases run
      | Ok u =>
        cases u
        head_reduce run
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
        cases Result.ok.inj run
        exact ⟨s1,s2,p1,p2,h0,h1,h2⟩
#print axioms reached
end AspisR1.FJj_RegularTrace
end
