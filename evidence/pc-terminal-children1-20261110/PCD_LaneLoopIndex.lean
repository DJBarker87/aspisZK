import PCD_LaneLoop
set_option autoImplicit false
namespace PCD_LaneLoop

theorem done_index (test : Nat → Bool) (level n out : Nat)
    (returned : scan test level n = .done out) : out = level+n := by
  induction n generalizing level out with
  | zero => simp only [scan, Scan.done.injEq] at returned; omega
  | succ n ih =>
    by_cases h : test level = true
    · rw [scan_continue test level n h] at returned
      have := ih (level+1) out returned
      omega
    · have hf : test level = false := by cases e : test level <;> simp_all
      rw [scan_reject test level n hf] at returned
      cases returned

/-- Every loop terminal is determined by its own comparison results. -/
theorem rejected_not_good (test : Nat → Bool) (level n whereFailed : Nat)
    (returned : scan test level n = .rejected whereFailed) : ¬good test level n := by
  intro all
  have done := (scan_done_iff test level n).2 all
  rw [returned] at done
  cases done
#print axioms done_index
#print axioms rejected_not_good
end PCD_LaneLoop
