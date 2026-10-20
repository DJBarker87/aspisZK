import FissionLoopStepSemanticsV1
import FinishRoundSelectorSemanticV1
import FinishRoundAlphaSemanticV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishFissionHelperAdapter
open _root_.AspisR1FinishRelationCurrent

def selectRoundAlphaModel (p : verifier.Prepared) (round : Usize) :
    Result aspis_core.field.WideExact := Array.index_usize p.alpha round

/-- The emitted helper's two selected records followed by the checked operation model.
    Backend arithmetic remains explicit in `ops`; selector inputs are the same records. -/
def finishRoundAdapter {W D : Type} (ops : FinishOps W D)
    (v : verifier.View) (p : verifier.Prepared)
    (claim : aspis_core.field.WideExact) (round : Usize) :
    Result (core.result.Result aspis_core.field.WideExact verifier.Error) := do
  let poly ← AspisR1FinishRoundSelectorSemantic.selectRoundPolyModel v round
  let alpha ← selectRoundAlphaModel p round
  verifier.finish_relation_round ops poly alpha claim round

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
  obtain ⟨poly, hpoly, hrest⟩ := bind_success _ _ _ h
  obtain ⟨alpha, halpha, hcall⟩ := bind_success _ _ _ hrest
  exact ⟨poly, alpha, hpoly, halpha,
    FinishCandidateEquations.round_equation ops faithful poly alpha claim out round hcall⟩

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
  · exact False.elim (by scalar_tac)
  · have hpoly1 : poly = v.round1 := hother.2
    have halpha1 := AspisR1FinishRoundAlphaSemantic.alpha_at_one p alpha halpha
    rw [hpoly1, halpha1] at heq
    exact heq

#print axioms finishRoundAdapter_success
#print axioms finishRoundAdapter_zero_equation
#print axioms finishRoundAdapter_one_equation
end AspisR1FinishFissionHelperAdapter
