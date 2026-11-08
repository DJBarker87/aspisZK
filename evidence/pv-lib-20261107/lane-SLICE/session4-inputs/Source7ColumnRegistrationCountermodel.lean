import PV_STX2_Source7ColumnRegistrationFixture
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7ColumnRegistrationCountermodel
open Aeneas Aeneas.Std PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_STX2_Source7EntryOwned PV_STX2_Source7EntrySelection
open PV_STX2_Source7ColumnRegistrationFixture
/-! Conditional on owner acceptance of the translator patch. The diagnostic
checks the existing entry contract, not the Rust implementation. -/
theorem entry (seed : OWNER) : Source7EntryOwned (state seed) foundation := by
  intro i
  by_cases h : i.val = 1
  · refine ⟨source1,1,single,?_,rfl,?_,rfl,?_⟩
    · simp [state,source0,source1]
    · rw [values_at,if_pos h]; decide
    · simpa only [values_at,if_pos h] using typed1 seed
  · refine ⟨source0,0,empty,?_,rfl,?_,rfl,?_⟩
    · simp [state,source0]
    · rw [values_at,if_neg h]; decide
    · simpa only [values_at,if_neg h] using typed0 seed
theorem slot_cases (seed : OWNER) (id : Nat) (h : Header)
    (read : lookup (state seed).world id = some h) :
    (id = 0 ∧ h = empty) ∨ (id = 1 ∧ h = single) := by
  change (if id = 0 then some empty else if id = 1 then some single else none) = some h at read
  split at read
  · cases read; exact Or.inl ⟨by assumption,rfl⟩
  · split at read
    · cases read; exact Or.inr ⟨by assumption,rfl⟩
    · cases read
def second : Fin foundation.c1.val.length := ⟨1,by simp [foundation]⟩
theorem first_selected (seed : OWNER) :
    identity (entry seed) (PV_STX2_Source7EntryAddress.first foundation) = 0 ∧
    header (entry seed) (PV_STX2_Source7EntryAddress.first foundation) = empty := by
  have len := PV_STX2_Source7EntryHeaderFacts.length (entry seed)
    (PV_STX2_Source7EntryAddress.first foundation)
  rw [values_at] at len
  change (header (entry seed) (PV_STX2_Source7EntryAddress.first foundation)).len = 0 at len
  rcases slot_cases seed _ _ (selected (entry seed) _).2.1 with h | h
  · exact h
  · rw [h.2] at len; contradiction
theorem second_selected (seed : OWNER) :
    identity (entry seed) second = 1 ∧ header (entry seed) second = single := by
  have len := PV_STX2_Source7EntryHeaderFacts.length (entry seed) second
  rw [values_at] at len
  change (header (entry seed) second).len = 1 at len
  rcases slot_cases seed _ _ (selected (entry seed) _).2.1 with h | h
  · rw [h.2] at len; contradiction
  · exact h
def refined (seed : OWNER) :
    PV_STX2_Source7EntryOwnedWellFormed.Source7EntryOwned'' (state seed) foundation :=
  ⟨⟨entry seed,by
    have selected0 := (selected (entry seed) (PV_STX2_Source7EntryAddress.first foundation)).1
    rw [(first_selected seed).1] at selected0
    rw [selected0]
    change (state seed).places (PV_STX2_Source7QBinding.ownerPlace
      ⟨0,(header (entry seed) (PV_STX2_Source7EntryAddress.first foundation)).pointer,[]⟩) = some 0
    rw [(first_selected seed).2]
    rfl⟩,wellFormed seed⟩
theorem missing_second (seed : OWNER) :
    (state seed).places (PV_STX2_Source7QBinding.ownerPlace
      ⟨0,(header (refined seed).registered.owned second).pointer,[]⟩) = none ∧
    (state seed).places (place (refined seed).registered.owned second) = some 1 := by
  constructor
  · change (state seed).places (PV_STX2_Source7QBinding.ownerPlace
      ⟨0,(header (entry seed) second).pointer,[]⟩) = none
    rw [(second_selected seed).2]
    rfl
  · have selected1 := (selected (entry seed) second).1
    rw [(second_selected seed).1] at selected1
    exact selected1
theorem not_all_registered (seed : OWNER) :
    ¬ (∀ i : Fin foundation.c1.val.length,
      (state seed).places (PV_STX2_Source7QBinding.ownerPlace
        ⟨0,(header (refined seed).registered.owned i).pointer,[]⟩) =
      (state seed).places (place (refined seed).registered.owned i)) := by
  intro all
  have bad := all second
  rw [(missing_second seed).1,(missing_second seed).2] at bad
  cases bad
#print axioms entry
#print axioms slot_cases
#print axioms first_selected
#print axioms second_selected
#print axioms refined
#print axioms missing_second
#print axioms not_all_registered
end PV_STX2_Source7ColumnRegistrationCountermodel
