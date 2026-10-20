import FinishRoundSelectorSemanticV1
import FinishRoundAlphaSemanticV1
import FinishCandidateEquations
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishFissionHelperAdapterV2
open _root_.AspisR1FinishRelationCurrent

def selectRoundAlphaModel (p : verifier.Prepared) (round : Usize) :
    Result aspis_core.field.WideExact := Array.index_usize p.alpha round

/-- Flat operation-parameterized body in the exact generated call order.
The generated Funs body is pinned separately; no raw external template is imported. -/
def finishRoundAdapter {W D : Type} (ops : FinishOps W D)
    (v : verifier.View) (p : verifier.Prepared)
    (claim : aspis_core.field.WideExact) (round : Usize) :
    Result (core.result.Result aspis_core.field.WideExact verifier.Error) := do
  let poly ← AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel v round
  let we ← ops.field poly 0#usize
  let we1 ← ops.field poly 4#usize
  let lhs ← ops.add we we1
  let m ← ops.quarter
  let rhs ← ops.mulM31 claim m
  let i ← 3#usize * round
  trace.value 15#u16 i lhs
  let i1 ← i + 1#usize
  trace.value 15#u16 i1 rhs
  let b ← core.cmp.PartialEq.ne.trait_default
    (aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact ops) lhs rhs
  if b then ok (core.result.Result.Err verifier.Error.Relation)
  else do
    let alpha ← selectRoundAlphaModel p round
    let claim1 ← ops.polynomial poly alpha
    let i2 ← i + 2#usize
    trace.value 15#u16 i2 claim1
    ok (core.result.Result.Ok claim1)

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private def alpha0Slot (p : verifier.Prepared) : aspis_core.field.WideExact :=
  p.alpha.val[0]'(by
    have hlen : (0#usize).val < (2#usize).val := by scalar_tac
    simpa [p.alpha.property] using hlen)

private def alpha1Slot (p : verifier.Prepared) : aspis_core.field.WideExact :=
  p.alpha.val[1]'(by
    have hlen : (1#usize).val < (2#usize).val := by scalar_tac
    simpa [p.alpha.property] using hlen)

theorem finishRoundAdapter_success {W D : Type} (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = .ok true → x = y)
    (v : verifier.View) (p : verifier.Prepared)
    (claim out : aspis_core.field.WideExact) (round : Usize)
    (h : finishRoundAdapter ops v p claim round = .ok (.Ok out)) :
    ∃ poly alpha,
      AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel v round = .ok poly ∧
      selectRoundAlphaModel p round = .ok alpha ∧
      FinishCandidateEquations.RoundEquation ops poly alpha claim out := by
  obtain ⟨poly, hpoly, h⟩ := bind_success _ _ _ h
  obtain ⟨x0, hx0, h⟩ := bind_success _ _ _ h
  obtain ⟨x4, hx4, h⟩ := bind_success _ _ _ h
  obtain ⟨lhs, hlhs, h⟩ := bind_success _ _ _ h
  obtain ⟨q, hq, h⟩ := bind_success _ _ _ h
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
    obtain ⟨alpha, halpha, h⟩ := bind_success _ _ _ h
    obtain ⟨out1, hout, h⟩ := bind_success _ _ _ h
    obtain ⟨idx2, _, h⟩ := bind_success _ _ _ h
    obtain ⟨_, _, h⟩ := bind_success _ _ _ h
    have houtEq : out1 = out :=
      core.result.Result.Ok.inj (Result.ok.inj h)
    subst out
    have hval : lhs = rhs :=
      FinishCandidateEquations.ne_guard_eq ops faithful lhs rhs hbad
    exact ⟨poly, alpha, hpoly, halpha,
      ⟨x0, x4, lhs, q, rhs, hx0, hx4, hlhs, hq, hrhs, hval, hout⟩⟩

theorem finishRoundAdapter_zero_equation {W D : Type} (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = .ok true → x = y)
    (v : verifier.View) (p : verifier.Prepared)
    (claim out : aspis_core.field.WideExact)
    (h : finishRoundAdapter ops v p claim 0#usize = .ok (.Ok out)) :
    FinishCandidateEquations.RoundEquation ops v.round0 (alpha0Slot p) claim out := by
  obtain ⟨poly, alpha, hpoly, halpha, heq⟩ :=
    finishRoundAdapter_success ops faithful v p claim out 0#usize h
  have hp := AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel_success v 0#usize poly hpoly
  rcases hp with hzero | hother
  · have hpoly0 : poly = v.round0 := hzero.2
    have halpha0 := AspisR1FinishRoundAlphaSemantic.alpha_at_zero p alpha halpha
    rw [hpoly0, halpha0] at heq
    exact heq
  · exact False.elim (hother.1 rfl)

theorem finishRoundAdapter_one_equation {W D : Type} (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = .ok true → x = y)
    (v : verifier.View) (p : verifier.Prepared)
    (claim out : aspis_core.field.WideExact)
    (h : finishRoundAdapter ops v p claim 1#usize = .ok (.Ok out)) :
    FinishCandidateEquations.RoundEquation ops v.round1 (alpha1Slot p) claim out := by
  obtain ⟨poly, alpha, hpoly, halpha, heq⟩ :=
    finishRoundAdapter_success ops faithful v p claim out 1#usize h
  have hp := AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel_success v 1#usize poly hpoly
  rcases hp with hzero | hother
  · have hbad : (1#usize : Usize) = 0#usize := hzero.1
    have : False := by scalar_tac
    exact False.elim this
  · have hpoly1 : poly = v.round1 := hother.2
    have halpha1 := AspisR1FinishRoundAlphaSemantic.alpha_at_one p alpha halpha
    rw [hpoly1, halpha1] at heq
    exact heq

#print axioms finishRoundAdapter_success
#print axioms finishRoundAdapter_zero_equation
#print axioms finishRoundAdapter_one_equation
end AspisR1FinishFissionHelperAdapterV2
