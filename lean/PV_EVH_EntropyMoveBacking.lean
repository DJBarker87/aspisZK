import PV_EVH_StackMove
set_option autoImplicit false
namespace PV_EVH_EntropyMoveBacking
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackRegions (Separate)
open PV_EVH_StackCleanup (sameKey)
open PV_EVH_StackMove (relocate)

/-- The two owned entropy-field relocations. This is NOT a complete native
Self move: mask_nonce/return-object layout, primitive observations and actual
compiler move association remain P. No source-slot destructor is fabricated. -/
def pair (field seed returnedField returnedSeed : Slot) (w : State) : State :=
  relocate seed returnedSeed (relocate field returnedField w)

theorem original_lookup (field seed returnedField returnedSeed original : Slot) (w : State)
    (hl : w.frame.live.find? (sameKey original.key) = some original)
    (hf : original.key ≠ field.key) (hs : original.key ≠ seed.key)
    (hrf : sameKey original.key returnedField = false)
    (hrs : sameKey original.key returnedSeed = false) :
    (pair field seed returnedField returnedSeed w).frame.live.find?
      (sameKey original.key) = some original :=
  PV_EVH_StackMove.original_lookup seed returnedSeed original _
    (PV_EVH_StackMove.original_lookup field returnedField original w hl hf hrf) hs hrs

theorem returned_backing (field seed returnedField returnedSeed original : Slot) (w : State)
    (hfs : Separate returnedSeed returnedField)
    (hsource : Separate returnedField seed)
    (hof : Separate original returnedField) (hos : Separate original returnedSeed)
    (i : Nat) (hif : i < returnedField.initialized)
    (his : i < returnedSeed.initialized) (hb : i < seed.initialized) :
    let v := PV_EVH_StackZero.drop original (pair field seed returnedField returnedSeed w)
    v.memory (returnedField.address+i) = w.memory (field.address+i) ∧
    v.memory (returnedSeed.address+i) = w.memory (seed.address+i) := by
  dsimp only
  constructor
  · rw [PV_EVH_StackZero.outside_preserved original _ _
      (PV_EVH_StackRegions.outside original returnedField hof i hif)]
    unfold pair
    rw [PV_EVH_StackMove.residue_outside seed returnedSeed _ _
      (PV_EVH_StackRegions.outside returnedSeed returnedField hfs i hif)]
    exact PV_EVH_StackMove.destination field returnedField w i hif
  · rw [PV_EVH_StackZero.outside_preserved original _ _
      (PV_EVH_StackRegions.outside original returnedSeed hos i his)]
    unfold pair
    rw [PV_EVH_StackMove.destination seed returnedSeed _ i his]
    exact PV_EVH_StackMove.residue_outside field returnedField w _
      (PV_EVH_StackRegions.outside returnedField seed hsource i hb)

theorem no_field_destructors (field seed returnedField returnedSeed : Slot) (w : State) :
    (pair field seed returnedField returnedSeed w).drops = w.drops ∧
    (pair field seed returnedField returnedSeed w).writes = w.writes ∧
    (pair field seed returnedField returnedSeed w).barriers = w.barriers := ⟨rfl,rfl,rfl⟩

#print axioms original_lookup
#print axioms returned_backing
#print axioms no_field_destructors
end PV_EVH_EntropyMoveBacking
