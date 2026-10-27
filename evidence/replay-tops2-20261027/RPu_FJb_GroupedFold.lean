import RPu_FJb_GroupedValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_GroupedFold
open FJb_MatrixModel (Values block fold)
open FJb_GroupedValues (grouped)
/-- The source traversal never revisits a group: its small symbolic fold is
exactly one matrix application per selected original group. -/
theorem value (n g : Nat) (v : Values) (hbound : g+n≤4)
    (j : Fin (16#usize).val) :
    fold n g v j=if g≤j.val/4 ∧ j.val/4 < g+n then grouped v j else v j := by
  induction n generalizing g v with
  | zero =>
    simp only [fold]
    rw [if_neg (by omega)]
  | succ n ih =>
    rw [fold,ih (g+1) (block v g) (by omega)]
    by_cases he : j.val/4=g
    · have hf : ¬(g+1≤j.val/4 ∧ j.val/4 < g+1+n) := by omega
      have hc : g≤j.val/4 ∧ j.val/4 < g+(n+1) := by omega
      rw [if_neg hf,if_pos hc]
      exact FJb_GroupedValues.inside v g j he
    · have hcond : (g+1≤j.val/4 ∧ j.val/4 < g+1+n) ↔
          (g≤j.val/4 ∧ j.val/4 < g+(n+1)) := by omega
      rw [FJb_GroupedValues.preserved v g j he,FJb_MatrixLocality.outside v g j he]
      simp only [hcond]

theorem full (v : Values) : fold 4 0 v=grouped v := by
  funext j
  have hj : j.val < 16 := j.isLt
  have hc : 0≤j.val/4 ∧ j.val/4 < 0+4 := by omega
  simpa only [if_pos hc] using value 4 0 v (by decide) j
#print axioms value
#print axioms full
end AspisR1.FJb_GroupedFold
end
