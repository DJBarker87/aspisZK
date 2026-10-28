import NBZ_DotPhase
set_option autoImplicit false
namespace NBZ_DotStages
/-- Native K067's accumulator precondition follows from the exact previously
returned fold values; it is not an additional restriction on a reached caller. -/
theorem prefix_folds (values : List Nat) (size : values.length≤6)
 (small : ∀ x∈values,x<2^34) : values.sum<6*(2^34) := by
 have bound : values.sum≤values.length*(2^34-1) := by
   induction values with
   | nil => simp
   | cons x xs ih =>
     have hx := small x List.mem_cons_self
     have ht := ih (by simp only [List.length_cons] at size;omega)
       (by intro y hy;exact small y (List.mem_cons_of_mem _ hy))
     simp only [List.sum_cons,List.length_cons,Nat.succ_mul]
     omega
 have count := Nat.mul_le_mul_right (2^34-1) size
 omega
/-- Every selected product within the actual 26-term grouping has the domain
required by the retained native integer fragment, on that SAME group's prefix. -/
theorem group_cell (xs block : List (Nat×Nat)) (size : xs.length=26)
 (canonical : ∀ x∈xs,x.1<2^31-1 ∧ x.2<2^31-1)
 (member : block∈NBW_DotWindows.windows 6 xs) (t : Nat) (active : t<block.length) :
 t<4 ∧ NBB_Phase.Bound t (NBZ_DotBounds.sumProducts (block.take t)) := by
 have width : block.length≤4 := NBW_DotWindows.extent 6 xs (by omega) block member
 have prefixLength : (block.take t).length=t := by
   simp only [List.length_take];omega
 have prefixCanon : ∀ x∈block.take t,x.1<2^31-1 ∧ x.2<2^31-1 := by
   intro x hx
   exact canonical x (NBW_DotWindows.member 6 xs block x member (List.mem_of_mem_take hx))
 have phase := NBZ_DotPhase.caller (block.take t) (by rw [prefixLength];omega) prefixCanon
 rw [prefixLength] at phase
 exact ⟨by omega,phase⟩
#print axioms prefix_folds
#print axioms group_cell
end NBZ_DotStages
