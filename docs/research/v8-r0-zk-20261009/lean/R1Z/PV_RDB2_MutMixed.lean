import R1Z.PV_RDB2_MutBorrow

namespace R1Z.PV_RDB2_MutMixed
set_option autoImplicit false
open PV_RDB2_MutBorrow

theorem disjoint_writes {T : Type} (cells : Nat → T) (a b : Handle) (x y : T)
    (different : a.index ≠ b.index) :
    PV_RDB2_MutBorrow.set (PV_RDB2_MutBorrow.set cells a.index x) b.index y = PV_RDB2_MutBorrow.set (PV_RDB2_MutBorrow.set cells b.index y) a.index x := by
  funext i
  by_cases ha : i = a.index
  · subst i
    simp [PV_RDB2_MutBorrow.set,different,Ne.symm different]
  · by_cases hb : i = b.index
    · subst i
      simp [PV_RDB2_MutBorrow.set,different,Ne.symm different]
    · simp only [PV_RDB2_MutBorrow.set,ha,hb,if_false]

theorem restore_commutes {T : Type} (current : Cursor T) (a b : Handle) (x y : T)
    (different : a.index ≠ b.index) :
    restore (restore current a x) b y = restore (restore current b y) a x := by
  exact congrArg (fun cells => {current with cells := cells})
    (disjoint_writes current.cells a b x y different)

theorem mixed_indices_distinct {T : Type} (c : Cursor T) (two : c.front+1 < c.back) :
    c.front ≠ c.back-1 := by omega

/-- Reading from the back after restoring the front obtains the original
back cell, and the iterator consumes it exactly once. -/
theorem back_after_front_write {T : Type} (c : Cursor T) (value : T)
    (two : c.front+1 < c.back) :
    nextBack (restore {c with front := c.front+1} ⟨c.front⟩ value) =
      some (c.cells (c.back-1),⟨c.back-1⟩,
        {restore {c with front := c.front+1} ⟨c.front⟩ value with back := c.back-1}) := by
  have different : c.back-1 ≠ c.front := by omega
  simp only [nextBack,restore,two,if_true,PV_RDB2_MutBorrow.set,different,if_false]

#print axioms disjoint_writes
#print axioms restore_commutes
#print axioms mixed_indices_distinct
#print axioms back_after_front_write
end R1Z.PV_RDB2_MutMixed
