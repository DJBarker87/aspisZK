import FinishCandidateExplicitOps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishRelationCurrent.FinishCandidateRoundSuccess
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem round_success {W D : Type} (ops : FinishOps W D)
    (poly : Slice U8) (alpha claim out : aspis_core.field.WideExact) (round : Usize)
    (h : verifier.finish_relation_round ops poly alpha claim round = ok (.Ok out)) :
    ∃ x0 x4 lhs quarter rhs,
      ops.field poly 0#usize = ok x0 ∧ ops.field poly 4#usize = ok x4 ∧
      ops.add x0 x4 = ok lhs ∧ ops.quarter = ok quarter ∧
      ops.mulM31 claim quarter = ok rhs ∧
      core.cmp.PartialEq.ne.trait_default
        (aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact ops) lhs rhs = ok false ∧
      ops.polynomial poly alpha = ok out := by
  unfold verifier.finish_relation_round at h
  obtain ⟨x0, hx0, h⟩ := bind_success _ _ _ h
  obtain ⟨x4, hx4, h⟩ := bind_success _ _ _ h
  obtain ⟨lhs, hlhs, h⟩ := bind_success _ _ _ h
  obtain ⟨quarter, hquarter, h⟩ := bind_success _ _ _ h
  obtain ⟨rhs, hrhs, h⟩ := bind_success _ _ _ h
  obtain ⟨idx, _, h⟩ := bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := bind_success _ _ _ h
  obtain ⟨idx1, _, h⟩ := bind_success _ _ _ h
  obtain ⟨_, _, h⟩ := bind_success _ _ _ h
  obtain ⟨bad, hbad, h⟩ := bind_success _ _ _ h
  cases bad with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨out1, hout, h⟩ := bind_success _ _ _ h
    obtain ⟨idx2, _, h⟩ := bind_success _ _ _ h
    obtain ⟨_, _, h⟩ := bind_success _ _ _ h
    cases h
    exact ⟨x0, x4, lhs, quarter, rhs, hx0, hx4, hlhs, hquarter, hrhs, hbad, hout⟩
#print axioms round_success
end AspisR1FinishRelationCurrent.FinishCandidateRoundSuccess
