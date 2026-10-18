import SemanticRoundAlphaSelectedCanonical

/-! Canonical selected-carrier challenges from the successful retained begin
caller. Reuses the actual semantic-call run, not an independent sampler model. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.ActualBeginSelectedCanonical
open r1_wire
abbrev SelectedCanonical := SemanticCallSelectedCanonical.SelectedCanonical
abbrev ToSelected := SemanticCallSelectedCanonical.toSelected

theorem begin_challenges_selected_canonical {H : Type}
    (D : aspis_core.Digest32 H) (pre : Prefix)
    (before after : SemanticTranscript H) (out : Challenges)
    (h : begin D pre before = ok (.Ok out, after)) :
    SelectedCanonical (ToSelected out.lambda) ∧
    SelectedCanonical (ToSelected out.chi) ∧
    SelectedCanonical (ToSelected out.theta) ∧
    SelectedCanonical (ToSelected out.mu) ∧
    SelectedCanonical (ToSelected out.eta) ∧
    ∀ i : Fin 10, SelectedCanonical (ToSelected
      (out.zc.val[i.val]'(by simpa [out.zc.property] using i.isLt))) := by
  obtain ⟨qs, hrun, hqs⟩ := BeginCalls.begin_success D pre before after out h
  have hall := SemanticRoundAlphaSelectedCanonical.run_values_canonical
    D pre BeginCalls.rows before after qs hrun
  rw [hqs] at hall
  refine ⟨hall _ (by simp [BeginCalls.challengeList]),
    hall _ (by simp [BeginCalls.challengeList]),
    hall _ (by simp [BeginCalls.challengeList]),
    hall _ (by simp [BeginCalls.challengeList]),
    hall _ (by simp [BeginCalls.challengeList]), ?_⟩
  intro i
  apply hall
  have hmem : out.zc.val[i.val]'(by
      simpa [out.zc.property] using i.isLt) ∈ out.zc.val := List.getElem_mem _
  simp only [BeginCalls.challengeList, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inl hmem)))

#print axioms begin_challenges_selected_canonical
end AspisR1PublicPreparation.ActualBeginSelectedCanonical
