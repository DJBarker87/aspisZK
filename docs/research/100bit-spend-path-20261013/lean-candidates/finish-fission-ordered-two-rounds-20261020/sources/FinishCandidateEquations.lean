import FinishCandidateOuterSuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishRelationCurrent.FinishCandidateEquations
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem ne_guard_eq {W D : Type} (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = ok true → x = y)
    (x y : aspis_core.field.WideExact)
    (h : core.cmp.PartialEq.ne.trait_default
      (aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact ops) x y = ok false) :
    x = y := by
  change (do let b ← ops.eq x y; ok (¬b)) = ok false at h
  obtain ⟨b, hb, h⟩ := bind_success _ _ _ h
  cases b with
  | false => cases h
  | true => exact faithful x y hb

def RoundEquation {W D : Type} (ops : FinishOps W D)
    (poly : Slice U8) (alpha claim out : aspis_core.field.WideExact) : Prop :=
  ∃ x0 x4 lhs q rhs,
    ops.field poly 0#usize = ok x0 ∧ ops.field poly 4#usize = ok x4 ∧
    ops.add x0 x4 = ok lhs ∧ ops.quarter = ok q ∧
    ops.mulM31 claim q = ok rhs ∧ lhs = rhs ∧ ops.polynomial poly alpha = ok out

theorem round_equation {W D : Type} (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = ok true → x = y)
    (poly : Slice U8) (alpha claim out : aspis_core.field.WideExact) (round : Usize)
    (h : verifier.finish_relation_round ops poly alpha claim round = ok (.Ok out)) :
    RoundEquation ops poly alpha claim out := by
  obtain ⟨x0,x4,lhs,q,rhs,h0,h4,ha,hq,hm,hne,hp⟩ :=
    FinishCandidateRoundSuccess.round_success ops poly alpha claim out round h
  exact ⟨x0,x4,lhs,q,rhs,h0,h4,ha,hq,hm,ne_guard_eq ops faithful lhs rhs hne,hp⟩

theorem s2_success_equations {W D : Type} (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = ok true → x = y)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit)) (hv : p.variant = transport.Variant.S2)
    (h : verifier.finish_relation ops v p a obs = ok (.Ok ())) :
    ∃ alpha0 claim1 alpha1 claim2 w sliced pair actual,
      Array.index_usize p.alpha 0#usize = ok alpha0 ∧
      RoundEquation ops v.round0 alpha0 p.claim claim1 ∧
      Array.index_usize p.alpha 1#usize = ok alpha1 ∧
      RoundEquation ops v.round1 alpha1 claim1 claim2 ∧
      ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok w) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.WideExact))
        p.alpha { «end» := 2#usize } = ok sliced ∧
      ops.pair w sliced v.final_message p.kappa = ok (.Ok pair) ∧ pair = claim2 ∧
      verifier.finish_query_dot ops v.final_message (alloc.vec.Vec.deref a.weights) = ok (.Ok actual) ∧
      actual = a.rhs ∧ a.next = 22#usize := by
  obtain ⟨a0,c1,a1,c2,w,sliced,pair,actual,h0,hr0,h1,hr1,hw,hs,hp,hnep,_,hd,hn,hned,_⟩ :=
    FinishCandidateOuterSuccess.s2_success_calls ops v p a obs hv h
  refine ⟨a0,c1,a1,c2,w,sliced,pair,actual,h0,
    round_equation ops faithful _ _ _ _ _ hr0,h1,
    round_equation ops faithful _ _ _ _ _ hr1,hw,hs,hp,
    ne_guard_eq ops faithful pair c2 hnep,hd,
    ne_guard_eq ops faithful actual a.rhs hned,?_⟩
  simpa only [bne_eq_false_iff_eq] using hn
#print axioms ne_guard_eq
#print axioms round_equation
#print axioms s2_success_equations
end AspisR1FinishRelationCurrent.FinishCandidateEquations
