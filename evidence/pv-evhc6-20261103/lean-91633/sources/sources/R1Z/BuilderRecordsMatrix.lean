import R1Z.BuilderRecordsArray

set_option autoImplicit false
namespace R1Z.BuilderRecordsArray
open Aeneas Aeneas.Std Result

/-- Lexicographic completed-cell invariant, avoiding concrete matrix reduction. -/
def Cells {n : Usize} (m target : Array (Array U32 8#usize) n)
    (level lane : Nat) : Prop :=
  ∀ i j, i < n.val → j < 8 → (i < level ∨ i = level ∧ j < lane) →
    (m.val[i]!).val[j]! = (target.val[i]!).val[j]!

theorem cells_step {n : Usize} (m target : Array (Array U32 8#usize) n)
    (level lane : Usize) (hl : level.val < n.val) (hj : lane.val < 8)
    (h : Cells m target level.val lane.val) :
    Cells (m.set level ((m.val[level.val]!).set lane
      (target.val[level.val]!).val[lane.val]!)) target level.val (lane.val + 1) := by
  intro i j hi hj' hc
  rw [set_get _ _ _ _ hl]
  by_cases e : i = level.val
  · rw [if_pos e, set_get _ _ _ _ (by simpa using hj)]
    split
    · next ej => subst i; subst j; rfl
    · next ej =>
        rw [← e]
        exact h i j hi hj' (Or.inr ⟨e, by omega⟩)
  · rw [if_neg e]
    exact h i j hi hj' (Or.inl (by omega))

theorem cells_next {n : Usize} (m target : Array (Array U32 8#usize) n)
    (level : Nat) (h : Cells m target level 8) : Cells m target (level + 1) 0 := by
  intro i j hi hj hc
  apply h i j hi hj
  omega

theorem cells_done {n : Usize} (m target : Array (Array U32 8#usize) n)
    (h : Cells m target n.val 0) : m = target := by
  apply BuilderRecordCanonical.array_ext
  intro i hi
  apply BuilderRecordCanonical.array_ext
  intro j hj
  exact h i j hi (by simpa using hj) (Or.inl hi)

#print axioms cells_step
#print axioms cells_next
#print axioms cells_done
end R1Z.BuilderRecordsArray
