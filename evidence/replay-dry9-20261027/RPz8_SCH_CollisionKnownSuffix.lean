import RPz8_SCH_CollisionAppend
set_option autoImplicit false
namespace AspisR1.SCH_CollisionKnownSuffix
open FS AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

/-- Exact first-read collision-event equivalence for removal of a replay
whose addresses were already read. No new collision charge is introduced. -/
theorem same (bad : I → Table I A → A → Prop) (t : Table I A)
    (prior suffix : List (I × A))
    (known : ∀ a ∈ suffix.map Prod.fst, a ∈ prior.map Prod.fst) :
    hitsBad bad t (prior ++ suffix) ↔ hitsBad bad t prior := by
  rw [SCH_CollisionAppend.append]
  have cached : ¬ hitsBad bad (SCH_TableAfter.after t prior) suffix := by
    apply SCH_CollisionAppend.cached
    intro q member
    exact SCH_TableAfter.read t prior q.1 (known q.1 (List.mem_map.mpr ⟨q,member,rfl⟩))
  exact or_iff_left cached

#print axioms same
end AspisR1.SCH_CollisionKnownSuffix
