import S9PairTermPrefixMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairTermChildrenV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem pair_term_at_success_children
    (ap1 : Array PW (4#usize)) (high : Array PQ (4#usize)) (i : PU)
    (perm : PU) (term : PW)
    (h : AspisR1S9PairTermPrefixMapV1.pairTermAt ap1 high i = .ok (perm,term)) :
    ∃ (x : PW) (a : PQ) (product : PW),
      Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM i = .ok perm ∧
      Array.index_usize ap1 perm = .ok x ∧
      Array.index_usize high i = .ok a ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x a = .ok product ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
        _root_.AspisR1S9PairCallerStepV1.weights.QUARTER = .ok term := by
  have hc := h
  unfold AspisR1S9PairTermPrefixMapV1.pairTermAt at hc
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM i) _ _ hc with
    ⟨p,hp,hc⟩
  rcases bind_success_inv (Array.index_usize ap1 p) _ _ hc with
    ⟨x,hx,hc⟩
  rcases bind_success_inv (Array.index_usize high i) _ _ hc with
    ⟨a,ha,hc⟩
  rcases bind_success_inv (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x a)
    _ _ hc with ⟨product,hm,hc⟩
  rcases bind_success_inv
      (AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
        _root_.AspisR1S9PairCallerStepV1.weights.QUARTER)
      _ _ hc with ⟨termResult,hm31,hc⟩
  have hlast := Result.ok.inj hc
  have hpEq : p = perm := congrArg Prod.fst hlast
  have htermEq : termResult = term := congrArg Prod.snd hlast
  subst p
  subst termResult
  exact ⟨x,a,product,hp,hx,ha,hm,hm31⟩

#print axioms pair_term_at_success_children

end AspisR1S9PairTermChildrenV1
