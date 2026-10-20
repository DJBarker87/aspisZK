import Aeneas
import FinishCandidateEquations
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishRoundSelectorSemantic
open _root_.AspisR1FinishRelationCurrent

def selectRoundPolyModel (v : verifier.View) (round : Usize) : Result (Slice U8) := do
  if round = 0#usize then ok v.round0 else ok v.round1

theorem selectRoundPolyModel_success (v : verifier.View) (round : Usize)
    (poly : Slice U8)
    (h : selectRoundPolyModel v round = .ok poly) :
    (round = 0#usize ∧ poly = v.round0) ∨
      (round ≠ 0#usize ∧ poly = v.round1) := by
  unfold selectRoundPolyModel at h
  by_cases hz : round = 0#usize
  · simp only [hz, ↓reduceIte, Result.ok.injEq] at h
    exact Or.inl ⟨hz, h.symm⟩
  · simp only [hz, ↓reduceIte, Result.ok.injEq] at h
    exact Or.inr ⟨hz, h.symm⟩

#print axioms selectRoundPolyModel_success
end AspisR1FinishRoundSelectorSemantic
