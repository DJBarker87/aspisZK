import CurrentCompactCallerModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.PrepareReachability
open AspisR1CurrentCaller

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Successful *current compact* preparation supplies its own selected View,
semantic verification, Prepared::new and post-scratch. No chosen child outputs,
child success, independent View parse, powers or canonicality premise. -/
theorem prepare_success (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (out : verifier.Prepared)
    (scratchIn scratchOut : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (h : verifier.candidate.prepare ops D pub proof hash none scratchIn=
      ok (.Ok out,scratchOut)) :
    ∃ (semantic y1 : Slice U8) (v : verifier.View) (sem : r1_semantic.Verified H),
      ops.op5 proof semantic y1=ok (.Ok v) ∧
      ops.op9 D pub v.semantic hash none=ok (.Ok sem) ∧
      ops.op8 D sem v hash scratchIn=ok (.Ok out,scratchOut) := by
  unfold verifier.candidate.prepare at h
  obtain ⟨i,hi,h⟩ := bind_success _ _ _ h
  obtain ⟨iy,hiy,h⟩ := bind_success _ _ _ h
  obtain ⟨n,hn,h⟩ := bind_success _ _ _ h
  obtain ⟨r,hr,h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.map_err,
      verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
      verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok logical =>
    simp only [core.result.Result.map_err,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨deref,hderef,h⟩ := bind_success _ _ _ h
    obtain ⟨split,hsplit,h⟩ := bind_success _ _ _ h
    obtain ⟨off0,hoff0,h⟩ := bind_success _ _ _ h
    obtain ⟨off1,hoff1,h⟩ := bind_success _ _ _ h
    obtain ⟨storedSemantic,hstoredSemantic,h⟩ := bind_success _ _ _ h
    obtain ⟨expSemantic,hexpSemantic,h⟩ := bind_success _ _ _ h
    rcases expSemantic with ⟨r,semantic1⟩
    dsimp only at h
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        verifier.Error.Insts.CoreConvertFromCodecError] at h
      change (do let e1 ← ops.op2 e;ok (core.result.Result.Err e1,scratchIn))=
        ok (.Ok out,scratchOut) at h
      obtain ⟨e1,he1,h⟩ := bind_success _ _ _ h
      cases h
    | Ok u =>
      cases u
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨off2,hoff2,h⟩ := bind_success _ _ _ h
      obtain ⟨storedY1,hstoredY1,h⟩ := bind_success _ _ _ h
      obtain ⟨expY1,hexpY1,h⟩ := bind_success _ _ _ h
      rcases expY1 with ⟨r,y11⟩
      dsimp only at h
      cases r with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          verifier.Error.Insts.CoreConvertFromCodecError] at h
        change (do let e1 ← ops.op2 e;ok (core.result.Result.Err e1,scratchIn))=
          ok (.Ok out,scratchOut) at h
        obtain ⟨e1,he1,h⟩ := bind_success _ _ _ h
        cases h
      | Ok u =>
        cases u
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        obtain ⟨semantic,hsemantic,h⟩ := bind_success _ _ _ h
        obtain ⟨y1,hy1,h⟩ := bind_success _ _ _ h
        obtain ⟨rv,hrv,h⟩ := bind_success _ _ _ h
        cases rv with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at h
          cases h
        | Ok v =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          obtain ⟨rs,hrs,h⟩ := bind_success _ _ _ h
          cases rs with
          | Err e =>
            simp only [core.result.Result.map_err,
              verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
              verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
              bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at h
            cases h
          | Ok sem =>
            simp only [core.result.Result.map_err,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTry.branch,verifier.mark] at h
            exact ⟨semantic,y1,v,sem,hrv,hrs,h⟩

#print axioms prepare_success
end AspisR1CurrentCaller.PrepareReachability
