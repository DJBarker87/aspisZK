import R1Z.ProverCommitCompletionAdapter

/-! A quotient representative preserves observable laws, but no deterministic
section alone supplies equal fibres over the original full-tape carrier. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTapeCompletion
open R0Z.JointView
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] [Fintype K] {F : Subfield K}

/-- An actually ignored H1 dependent-row limb. -/
def hiddenCell : Hidden := ⟨.inr (1,0,0), ⟨rfl, Or.inl rfl⟩⟩

theorem section_missing (choose : SourceTape K F → Padding K F) (s : SourceTape K F) :
    ∃ t : Tape K F, ∀ x : SourceTape K F, complete x (choose x) ≠ t := by
  let pad := Function.update (choose s) hiddenCell (choose s hiddenCell + 1)
  refine ⟨complete s pad, ?_⟩
  intro x eq
  have visible := congrArg project eq
  rw [project_complete, project_complete] at visible
  subst x
  have hidden := congrFun (congrArg padding eq) hiddenCell
  rw [padding_complete, padding_complete] at hidden
  have impossible : choose s hiddenCell = choose s hiddenCell + 1 := by
    simpa only [pad, Function.update_self] using hidden
  exact one_ne_zero (add_left_cancel (a := choose s hiddenCell)
    (show choose s hiddenCell + 1 = choose s hiddenCell + 0 by rw [← impossible, add_zero]))

/-- Equal fibres for raw tapes cannot follow from a uniform quotient alone.
A true protocol quotient endpoint, or additional source randomness, is needed. -/
theorem deterministic_section_not_equal_fibres
    (choose : SourceTape K F → Padding K F) (s : SourceTape K F) :
    ¬ ∃ cF : Nat, ∀ t : Tape K F,
      (Finset.univ.filter (fun x : SourceTape K F => complete x (choose x) = t)).card = cF := by
  rintro ⟨cF, uniform⟩
  obtain ⟨missing, absent⟩ := section_missing choose s
  have empty : (Finset.univ.filter (fun x : SourceTape K F =>
      complete x (choose x) = missing)) = ∅ := by
    ext x
    simp [absent x]
  have zero : cF = 0 := by
    have eq := uniform missing
    rw [empty, Finset.card_empty] at eq
    exact eq.symm
  have positive : 0 < (Finset.univ.filter (fun x : SourceTape K F =>
      complete x (choose x) = complete s (choose s))).card := by
    apply Finset.card_pos.mpr
    exact ⟨s, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  rw [uniform, zero] at positive
  exact (Nat.lt_irrefl 0) positive

#print axioms section_missing
#print axioms deterministic_section_not_equal_fibres
end R1Z.ProverCommitTapeCompletion
