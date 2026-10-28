import NCV_ArrayRun
set_option autoImplicit false
namespace NDB_RejectInduction
open Aeneas Aeneas.Std Result
/-- Stop at the first rejecting row. No observations of any later row are required. -/
theorem run {A B : Type} [Inhabited A] {n : Usize}
    (body : (Array A n × Usize) → Result (ControlFlow (Array A n × Usize) B))
    (row : Nat → A) (bad : Nat) (failure : B)
    (steps : ∀ (a : Array A n) (i : Usize), i.val<bad → ∃ next : Usize,
      next.val=i.val+1 ∧ body (a,i)=ok (.cont (a.set i (row i.val),next)))
    (reject : ∀ (a : Array A n) (i : Usize), i.val=bad → body (a,i)=ok (.done failure))
    (a : Array A n) (i : Usize) (bound : i.val ≤ bad) :
    loop body (a,i)=ok failure := by
  have all : ∀ k : Nat, ∀ (a : Array A n) (i : Usize), i.val ≤ bad → bad-i.val=k →
      loop body (a,i)=ok failure := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a i hi hk
      by_cases done : i.val=bad
      · exact NCV_Loop.done _ _ _ (reject a i done)
      · obtain ⟨next,value,step⟩:=steps a i (by omega)
        rw [NCV_Loop.cont _ _ _ step]
        exact ih (bad-next.val) (by omega) _ next (by omega) rfl
  exact all (bad-i.val) a i bound rfl
#print axioms run
end NDB_RejectInduction
