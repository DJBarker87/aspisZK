import ARR_OffPath
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_FiniteFresh
/-- Symbolic cardinality proof on an ABSTRACT finite type. Instantiating this
lemma never enumerates a concrete large function-space universe. -/
theorem missing {S X : Type} [Fintype S] [DecidableEq X]
    (f : S → X) (injection : Function.Injective f) (log : List X)
    (bound : log.length < Fintype.card S) : ∃ s : S, f s ∉ log := by
  classical
  by_contra none
  have all : ∀ s : S, f s ∈ log := by
    simpa only [not_exists,not_not] using none
  have subset : (Finset.univ.image f : Finset X) ⊆ log.toFinset := by
    intro x member
    obtain ⟨s,_,same⟩ := Finset.mem_image.mp member
    rw [← same]
    exact List.mem_toFinset.mpr (all s)
  have count := (Finset.card_le_card subset).trans (List.toFinset_card_le log)
  rw [Finset.card_image_of_injective _ injection,Finset.card_univ] at count
  omega
#print axioms missing
end AspisR1.ARR_FiniteFresh
end
