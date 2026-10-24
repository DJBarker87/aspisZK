import CurrentCompactPrepareReachabilityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.PrepareCodecCalls
open AspisR1CurrentCaller

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The same complete successful preparation supplies both actual codec
calls and all downstream child calls. No length law, allocation length,
chosen View or independent successful child execution is a premise. -/
theorem prepare_codec_calls (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (out : verifier.Prepared)
    (scratchIn scratchOut : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (h : verifier.candidate.prepare ops D pub proof hash none scratchIn=ok (.Ok out,scratchOut)) :
    ∃ (off0 off1 off2 : Usize)
      (storedSemantic initialSemantic expandedSemantic storedY1 initialY1 expandedY1 semantic y1 : Slice U8)
      (v : verifier.View) (sem : r1_semantic.Verified H),
      compact.OFF_SEMANTIC ops=ok off0 ∧ compact.OFF_Y1 ops=ok off1 ∧
      compact.OFF_INACTIVE ops=ok off2 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=off0,«end»:=off1}=ok storedSemantic ∧
      ops.op10 storedSemantic initialSemantic=ok (.Ok (),expandedSemantic) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=off1,«end»:=off2}=ok storedY1 ∧
      ops.op11 storedY1 initialY1=ok (.Ok (),expandedY1) ∧
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
    cases r with
    | Err e =>
      change (do
        let r4 ← (do let e1 ← ops.op2 e;ok (core.result.Result.Err e1))
        ok (r4,scratchIn))=ok (.Ok out,scratchOut) at h
      obtain ⟨r4,hr4,h⟩ := bind_success _ _ _ h
      obtain ⟨e1,he1,hr4⟩ := bind_success _ _ _ hr4
      cases hr4
      cases h
    | Ok u =>
      cases u
      obtain ⟨off2,hoff2,h⟩ := bind_success (compact.OFF_INACTIVE ops) _ _ h
      obtain ⟨storedY1,hstoredY1,h⟩ := bind_success _ _ _ h
      obtain ⟨expY1,hexpY1,h⟩ := bind_success _ _ _ h
      rcases expY1 with ⟨r,y11⟩
      cases r with
      | Err e =>
        change (do
          let r4 ← (do let e1 ← ops.op2 e;ok (core.result.Result.Err e1))
          ok (r4,scratchIn))=ok (.Ok out,scratchOut) at h
        obtain ⟨r4,hr4,h⟩ := bind_success _ _ _ h
        obtain ⟨e1,he1,hr4⟩ := bind_success _ _ _ hr4
        cases hr4
        cases h
      | Ok u =>
        cases u
        obtain ⟨semantic,hsemantic,h⟩ := bind_success
          (alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
            (deref.2 (split.2 (semantic1,y11))) {«end»:=i}) _ _ h
        obtain ⟨y1,hy1,h⟩ := bind_success _ _ _ h
        obtain ⟨rv,hrv,h⟩ := bind_success _ _ _ h
        cases rv with
        | Err e =>
          change ok (core.result.Result.Err e,scratchIn)=ok (.Ok out,scratchOut) at h
          cases h
        | Ok v =>
          obtain ⟨rs,hrs,h⟩ := bind_success (ops.op9 D pub v.semantic hash none) _ _ h
          cases rs with
          | Err e =>
            change ok (core.result.Result.Err verifier.Error.Semantic,scratchIn)=
              ok (.Ok out,scratchOut) at h
            cases h
          | Ok sem =>
            change ops.op8 D sem v hash scratchIn=ok (.Ok out,scratchOut) at h
            exact ⟨off0,off1,off2,storedSemantic,split.1.1,semantic1,storedY1,split.1.2,y11,
              semantic,y1,v,sem,hoff0,hoff1,hoff2,hstoredSemantic,hexpSemantic,hstoredY1,hexpY1,hrv,hrs,h⟩

#print axioms prepare_codec_calls
end AspisR1CurrentCaller.PrepareCodecCalls
