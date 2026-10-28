import NBY_CountDomains

set_option autoImplicit false
namespace AspisR1.NBY_CountExecution
open MultiproofConeLiveOrder MultiproofConeCountPhysical
attribute [local instance] Classical.propDecidable

/-- Propagate the reached accumulator bound through the inherited SAME-key
scan/write execution. The next prestate is the previous poststate; no final
count or row correspondence is added as a premise. -/
theorem rows_spent (fuel depth : Nat) (key : Nat → Nat) (n i w count : Nat)
    (safe : w ≤ i) (bound : i ≤ n) (ordered : Strict key i n)
    (spent : count ≤ 16*depth+i) :
    (NBJ_CountRows.nativeRows fuel key n i w count).2 ≤ 16*depth+n := by
  induction fuel generalizing key i w count with
  | zero =>
    simp only [NBJ_CountRows.nativeRows]
    omega
  | succ fuel ih =>
    by_cases active : i < n
    · have group := NBI_CountScan.scan_group key n i active ordered
      have domain := NBI_CountScan.binary_group key n i active ordered
      dsimp only at group domain
      let stop := if i+1 < n ∧ key (i+1)/2 = key i/2 then i+2 else i+1
      have advancing : i < stop := domain.1
      have endBound : stop ≤ n := domain.2.1
      have nextSpent : count+(2-(stop-i)) ≤ 16*depth+stop :=
        NBY_CountDomains.row_preserves depth i stop count ⟨group.2.1,group.2.2⟩ advancing spent
      have nextOrder : Strict (write key i w) stop n := by
        intro a b lo asc hi
        have aw : a ≠ w := by omega
        have bw : b ≠ w := by omega
        simp only [write,if_neg aw,if_neg bw]
        exact ordered a b (by omega) asc hi
      rw [NBJ_CountRows.nativeRows,if_pos active,group.1]
      exact ih (write key i w) stop (w+1) _ (by omega) endBound nextOrder nextSpent
    · simp only [NBJ_CountRows.nativeRows,if_neg active]
      omega

#print axioms rows_spent
end AspisR1.NBY_CountExecution
