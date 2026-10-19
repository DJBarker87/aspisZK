import FinishCandidateExplicitOps
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FinishRelationCurrent.FinishCandidateDotTrace
abbrev E := aspis_core.field.WideExact
abbrev K := aspis_core.field.QM31
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem body_cont {W D : Type} (ops : FinishOps W D)
    (fm : Slice U8) (ws : Slice K) (dot dot1 : D) (j j1 : Usize)
    (h : verifier.finish_query_dot_loop.body ops fm ws dot j = .ok (.cont (dot1,j1))) :
    j < ws.len ∧ ∃ x q, ops.field fm j = .ok x ∧ Slice.index_usize ws j = .ok q ∧
      ops.pushDot dot x q = .ok (.Ok (), dot1) ∧
      (j + 1#usize : Result Usize) = .ok j1 := by
  unfold verifier.finish_query_dot_loop.body at h
  by_cases hj : j < ws.len
  · simp only [Slice.len, hj, ↓reduceIte] at h
    obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hq,h⟩ := bind_success _ _ _ h
    obtain ⟨pair,hp,h⟩ := bind_success _ _ _ h
    rcases pair with ⟨r,d⟩
    cases r with
    | Err err =>
      cases err
      simp [core.result.Result.map_err,
        verifier.finish_query_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        verifier.finish_query_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at h
    | Ok u =>
      cases u
      change (do let n ← (j + 1#usize : Result Usize)
                 .ok (ControlFlow.cont (β := D × Option (core.result.Result E verifier.Error)) (d,n))) =
          .ok (ControlFlow.cont (dot1,j1)) at h
      obtain ⟨n,hn,h⟩ := bind_success _ _ _ h
      have heq : (d,n) = (dot1,j1) := by simpa using h
      rcases Prod.mk.inj heq with ⟨rfl,rfl⟩
      exact ⟨hj,x,q,hx,hq,hp,hn⟩
  · simp [Slice.len, hj] at h

theorem body_done_none {W D : Type} (ops : FinishOps W D)
    (fm : Slice U8) (ws : Slice K) (dot dot1 : D) (j : Usize)
    (h : verifier.finish_query_dot_loop.body ops fm ws dot j = .ok (.done (dot1,none))) :
    ¬j < ws.len ∧ dot1 = dot := by
  unfold verifier.finish_query_dot_loop.body at h
  by_cases hj : j < ws.len
  · simp only [Slice.len, hj, ↓reduceIte] at h
    obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hq,h⟩ := bind_success _ _ _ h
    obtain ⟨pair,hp,h⟩ := bind_success _ _ _ h
    rcases pair with ⟨r,d⟩
    cases r with
    | Err err =>
      cases err
      simp [core.result.Result.map_err,
        verifier.finish_query_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        verifier.finish_query_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at h
    | Ok u =>
      cases u
      change (do let n ← (j + 1#usize : Result Usize)
                 .ok (ControlFlow.cont (β := D × Option (core.result.Result E verifier.Error)) (d,n))) =
          .ok (ControlFlow.done (dot1,none)) at h
      obtain ⟨n,hn,h⟩ := bind_success _ _ _ h
      simp at h
  · simp [Slice.len, hj] at h
    exact ⟨hj,h.symm⟩
#print axioms body_cont
#print axioms body_done_none
end AspisR1FinishRelationCurrent.FinishCandidateDotTrace
