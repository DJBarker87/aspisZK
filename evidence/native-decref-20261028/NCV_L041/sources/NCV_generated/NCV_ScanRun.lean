import NCV_Loop
set_option autoImplicit false
namespace NCV_ScanRun
open Aeneas Aeneas.Std Result

theorem none (body : Usize → Result (ControlFlow Usize (Option Bool))) (n : Nat)
    (steps : ∀ i : Usize, i.val<n → ∃ next : Usize, next.val=i.val+1 ∧ body i=ok (.cont next))
    (terminal : ∀ i : Usize, n ≤ i.val → body i=ok (.done none))
    (i : Usize) (bound : i.val ≤ n) : loop body i=ok none := by
  have all : ∀ k : Nat, ∀ j : Usize, j.val ≤ n → n-j.val=k → loop body j=ok none := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hj hk
      by_cases done : n ≤ j.val
      · exact NCV_Loop.done _ _ _ (terminal j done)
      · obtain ⟨next,value,step⟩:=steps j (by omega)
        rw [NCV_Loop.cont _ _ _ step]
        exact ih (n-next.val) (by omega) next (by omega) rfl
  exact all (n-i.val) i bound rfl

#print axioms none
end NCV_ScanRun
